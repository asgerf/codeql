/**
 * Library that performs the near-equivalent of type-tracking every LocalSourceNode.
 */

/**
 * Language-specific configuration for universal type-tracking.
 */
signature module UniversalTypeTrackingSig {
  /**
   * A node in the type-tracking graph. Should only include local source nodes.
   */
  class Node;

  /**
   * A key to associate with stores and loads.
   */
  class Content;

  /**
   * A content filter, restricting what kinds of content may flow through certain edges.
   */
  class ContentFilter {
    /** Gets a content matched by this filter. */
    Content getAMatchingContent();

    /** Gets a string representation of this filter. */
    string toString();
  }

  /**
   * Summary of value-transforming steps.
   *
   * This can be used to support partial invocation, and will usually include
   * the number of positional parameters that have been bound by partial calls.
   */
  class Transformation {
    /**
     * Gets the transformation representing this one followed by `other`, if any.
     */
    Transformation append(Transformation other);

    /** Gets a string representation of this partial call state. */
    string toString();

    /**
     * Holds if this is the empty transformation, that is, an ordinary value-transforming step.
     *
     * This transformation value must exist, but should not be used in `transformStep` since it
     * is effectively a `levelStep`.
     */
    predicate isEmpty();
  }

  /**
   * Holds if `pred` is stored in the `key` content of `succ`.
   */
  predicate storeStep(Node pred, Node succ, Content key);

  /**
   * Holds if the `key` content of `pred` is loaded into `succ`.
   */
  predicate loadStep(Node pred, Node succ, Content key);

  /**
   * Holds if the `loadKey` content of `pred` is stored in the `storeKey` content of `succ`.
   */
  predicate loadStoreStep(Node pred, Node succ, Content loadKey, Content storeKey);

  /**
   * Holds if `pred` flows to `succ` using local flow.
   */
  predicate levelStep(Node pred, Node succ);

  /**
   * Holds if `pred -> succ` is a step from argument to a parameter, not including receiver/self parameters.
   */
  predicate callStep(Node pred, Node succ);

  /**
   * Holds if `pred -> succ` is a step that preserves contents matching `filter`.
   */
  predicate withContentStep(Node pred, Node succ, ContentFilter filter);

  /**
   * Holds if `pred -> succ` is a step that preserves everything except contents matching `filter`.
   */
  predicate withoutContentStep(Node pred, Node succ, ContentFilter filter);

  /**
   * Holds if `pred -> succ` is a return step.
   */
  predicate returnStep(Node pred, Node succ);

  /**
   * Holds if `pred -> succ` is a jump step.
   */
  predicate jumpStep(Node pred, Node succ);

  /**
   * Holds if the value in `pred` is transformed according to `transform` and flows to `succ`.
   */
  predicate transformStep(Node pred, Node succ, Transformation transform);

  /**
   * Holds if `node` is a parameter and so should not be tracked out of returns.
   *
   * The rationale for this is that the only use-case for tracking this is to reason about
   * calls to the enclosing callable, from an unseen call site. Thus, tracking it to known
   * call sites is not relevant.
   */
  predicate isParameterLike(Node node);

  /**
   * Holds if `node` should be tracked.
   */
  predicate shouldTrack(Node node);
}

/**
 * Module for performing forward type-tracking of all local source nodes.
 */
module UniversalTypeTrackingGen<UniversalTypeTrackingSig S> {
  private import S

  /**
   * Gets a content that is used in a store.
   */
  private Content getAStoreKey() {
    storeStep(_, _, result)
    or
    loadStoreStep(_, _, _, result)
  }

  private newtype TSummaryFilter =
    MkNoFilter() or
    MkNegativeFilter(ContentFilter filter)

  /**
   * A summary has either no filter, or a negative content filter.
   */
  class SummaryFilter extends TSummaryFilter {
    /** Gets the content filter, if any. */
    ContentFilter getNegativeFilter() { this = MkNegativeFilter(result) }

    /** Holds if this is no filter. */
    predicate isEmpty() { this = MkNoFilter() }

    /** Gets a string representation of this filter. */
    string toString() {
      result = "without " + this.getNegativeFilter().toString()
      or
      result = "no-filter" and this.isEmpty()
    }

    /** Gets a filter that matches everything matched by both filters. */
    pragma[nomagic]
    SummaryFilter append(SummaryFilter other) {
      // At the time of writing, there is only one non-empty filter
      this = other and result = this
      or
      other = MkNoFilter() and result = this
      or
      this = MkNoFilter() and result = other
    }

    /** Holds if `content` is permitted by this filter. */
    pragma[nomagic]
    predicate permitsContent(Content content) {
      content = getAStoreKey() and
      (
        exists(ContentFilter filter |
          this = MkNegativeFilter(filter) and not filter.getAMatchingContent() = content
        )
        or
        this instanceof MkNoFilter
      )
    }
  }

  private newtype TSummary =
    MkSummary(boolean hasReturn, boolean hasCall, SummaryFilter filter, Transformation transform) {
      hasReturn = [true, false] and
      hasCall = [true, false] and
      (
        // Transformations and content filters are mutually exclusive
        transform.isEmpty()
        or
        filter.isEmpty()
      )
    }

  /** A summary of the steps needed to propagate a value somewhere. */
  class Summary extends TSummary {
    /** Gets the `return` bit. */
    boolean getReturn() { this = MkSummary(result, _, _, _) }

    /** Gets the `call` bit. */
    boolean getCall() { this = MkSummary(_, result, _, _) }

    /** Gets the summary of the content filters seen on the path. */
    SummaryFilter getFilter() { this = MkSummary(_, _, result, _) }

    /** Gets the summary of the transformations seen on this path. */
    Transformation getTransformation() { this = MkSummary(_, _, _, result) }

    /** Gets this summary with a call step appended. */
    pragma[nomagic]
    Summary appendCall() {
      result = MkSummary(this.getReturn(), true, this.getFilter(), this.getTransformation())
    }

    /** Gets this summary with a return step appended. */
    pragma[nomagic]
    Summary appendReturn() {
      this.getCall() = false and
      result = MkSummary(true, false, this.getFilter(), _)
    }

    /** Gets this summary with a jump step appended. */
    pragma[nomagic]
    Summary appendJump() {
      result = MkSummary(this.getReturn(), false, this.getFilter(), this.getTransformation())
    }

    /** Gets this summary with a negative content filter appended. */
    pragma[nomagic]
    Summary appendWithoutContent(ContentFilter filter) {
      result =
        MkSummary(this.getReturn(), this.getCall(),
          this.getFilter().append(MkNegativeFilter(filter)), this.getTransformation())
    }

    /** Gets this summary with a transformation appended. */
    pragma[nomagic]
    Summary appendTransformation(Transformation transform) {
      result =
        MkSummary(this.getReturn(), this.getCall(), this.getFilter(),
          this.getTransformation().append(transform))
    }

    /** Gets this summary with the other summary appended. */
    pragma[nomagic]
    Summary append(Summary other) {
      this.getCall().booleanAnd(other.getReturn()) = false and
      result =
        MkSummary(this.getReturn().booleanOr(other.getReturn()), //
          this.getCall().booleanOr(other.getCall()), //
          this.getFilter().append(other.getFilter()), //
          this.getTransformation().append(other.getTransformation()))
    }

    /** Holds if this summary permits flow of the given `content`. */
    pragma[nomagic]
    predicate permitsContent(Content content) {
      this.getFilter().permitsContent(content) and
      this.getTransformation().isEmpty()
    }

    /** Gets this summary without any content filter. */
    pragma[nomagic]
    Summary withoutFilter() {
      result = MkSummary(this.getReturn(), this.getCall(), MkNoFilter(), this.getTransformation())
    }

    /** Gets this summary without a filter, but only if it it currently permits `content`. */
    pragma[nomagic]
    Summary popContent(Content content) {
      this.permitsContent(content) and
      result = this.withoutFilter()
    }

    private string getToStringPart(int i) {
      i = 0 and
      this.getReturn() = true and
      result = "return"
      or
      i = 1 and
      this.getCall() = true and
      result = "call"
      or
      i = 2 and
      not this.getFilter() = MkNoFilter() and
      result = this.getFilter().toString()
      or
      i = 3 and
      not this.getTransformation().isEmpty() and
      result = this.getTransformation().toString()
    }

    /** Gets a string representation of this summary. */
    string toString() {
      result = strictconcat(int i | | this.getToStringPart(i) order by i, ", ")
      or
      not exists(this.getToStringPart(_)) and
      result = "empty"
    }
  }

  /**
   * Holds if `node` should not be tracked out of returns, because such flow is never relevant.
   */
  pragma[nomagic]
  private predicate isIrrelevantForReturnFlow(Node node) {
    isParameterLike(node) and
    not storeStep(_, node, _) and
    not loadStoreStep(_, node, _, _)
  }

  /**
   * Holds if `node` should be tracked with the given initial `summary`.
   */
  private predicate initialState(Node node, Summary summary) {
    shouldTrack(node) and
    summary.getReturn() = false and
    summary.getFilter() = MkNoFilter() and
    if isIrrelevantForReturnFlow(node) then summary.getCall() = true else summary.getCall() = false
  }

  /**
   * Gets a node which `node` can flow to, along a path summarized by `summary`.
   */
  pragma[noopt]
  Node trackNode(Node node, Summary summary) {
    initialState(node, summary) and
    result = node
    or
    exists(Node mid, Summary prevSummary | mid = trackNode(node, prevSummary) |
      callStep(mid, result) and
      summary = prevSummary.appendCall()
      or
      returnStep(mid, result) and
      summary = prevSummary.appendReturn()
      or
      levelStep(mid, result) and
      summary = prevSummary
      or
      jumpStep(mid, result) and
      summary = prevSummary.appendJump()
      or
      exists(ContentFilter filter |
        withoutContentStep(mid, result, filter) and
        summary = prevSummary.appendWithoutContent(filter)
      )
      or
      exists(Transformation transform |
        transformStep(mid, result, transform) and
        summary = prevSummary.appendTransformation(transform)
      )
    )
    or
    exists(Summary prev, Summary next |
      result = trackNodeStep(node, prev, next) and
      summary = prev.append(next)
    )
  }

  /**
   * Gets a node which `node` can flow to, along a path summarized by `prev.append(next)`.
   */
  pragma[nomagic]
  private Node trackNodeStep(Node node, Summary prev, Summary next) {
    // This join is doubly recursive, so we can't use `pragma[noopt]` here without
    // scanning one of the `#prev` relations (which is expensive).
    // We also can't do the .append() here due to a bad outlining performed by the optimizer.
    exists(Node mid |
      mid = trackNode(node, prev) and
      derivedStep(mid, result, next)
    )
  }

  /**
   * Holds if `pred` can flow to `succ` via `summary`, as a result matching a store
   * and load edge, or similar.
   */
  pragma[noopt]
  private predicate derivedStep(Node pred, Node succ, Summary summary) {
    exists(Node obj, Node objDst, Content content, Summary objSummary |
      objDst = trackNode(obj, objSummary) and
      storeStep(pred, obj, content) and
      summary = objSummary.popContent(content) and
      loadStep(objDst, succ, content)
    )
    or
    // pred --(store)--> obj --(trackNode)--> objDst --(indirectLoad) --> succ
    exists(Node obj, Summary prev, Summary tmp, Summary next, Content content |
      succ = trackNodeToIndirectLoad(obj, prev, next, content) and
      storeStep(pred, obj, content) and
      tmp = prev.popContent(content) and
      summary = tmp.append(next)
    )
  }

  /**
   * Holds if the `content` of `pred` can flow to `succ` via one or more load-store
   * or with-content steps, followed by a load step.
   */
  pragma[noopt]
  private predicate indirectLoad(Node pred, Node succ, Summary summary, Content content) {
    // pred --(loadStore)--> obj --(trackNode) --> objDst --(loadStep)--> succ
    exists(Node obj, Node objDst, Content midContent, Summary objSummary |
      objDst = trackNode(obj, objSummary) and
      loadStoreStep(pred, obj, content, midContent) and
      summary = objSummary.popContent(midContent) and
      loadStep(objDst, succ, midContent)
    )
    or
    // pred --(loadStore)--> obj --(trackNode) --> objDst --(indirectLoad)--> succ
    exists(Node obj, Content midContent, Summary prev, Summary tmp, Summary next |
      succ = trackNodeToIndirectLoad(obj, prev, next, midContent) and
      loadStoreStep(pred, obj, content, midContent) and
      tmp = prev.popContent(midContent) and
      summary = tmp.append(next)
    )
    or
    // pred --(withContent)--> obj --(trackNode) --> objDst --(loadStep)--> succ
    exists(Node obj, Node objDst, ContentFilter filter |
      objDst = trackNode(obj, summary) and
      loadStep(objDst, succ, content) and
      filter.getAMatchingContent() = content and
      withContentStep(pred, obj, filter) and
      summary.permitsContent(content)
    )
    or
    // pred --(withContent)--> obj --(trackNode) --> objDst --(indirectLoad)--> succ
    exists(Node obj, Summary prev, Summary next, ContentFilter filter |
      succ = trackNodeToIndirectLoad(obj, prev, next, content) and
      filter.getAMatchingContent() = content and
      withContentStep(pred, obj, filter) and
      prev.permitsContent(content) and
      summary = prev.append(next)
    )
  }

  pragma[nomagic]
  private Node trackNodeToIndirectLoad(Node obj, Summary prev, Summary next, Content content) {
    // Factored due to mutual recursion. See `trackNodeStep`.
    exists(Node objDst |
      objDst = trackNode(obj, prev) and
      indirectLoad(objDst, result, next, content)
    )
  }

  cached
  private module Cached {
    /**
     * Gets a node reachable from `source`.
     */
    cached
    Node trackNode(Node source) { result = trackNode(source, _) }

    /**
     * Gets a node which flows to `sink`.
     */
    cached
    Node backtrackNode(Node sink) { trackNode(result) = sink }
  }

  import Cached
}
