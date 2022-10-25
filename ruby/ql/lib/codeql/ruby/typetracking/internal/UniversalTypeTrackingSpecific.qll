private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowPrivate as Private
private import codeql.ruby.typetracking.TypeTrackerSpecific as TT
private import UniversalTypeTrackingImpl

/**
 * Module providing language-specific configuration to `CoarseFlow`.
 *
 * It written like this to simplify eventual migration to a parameterized module,
 * though it's not 100% ready to be parameterized yet.
 */
module UniversalTypeTrackingForRuby implements UniversalTypeTrackingSig {
  class Node = TT::TypeTrackingNode;

  // Note: this is a ContentSet under the hood, but universal type-trackign considers all contents to be disjoint.
  class Content = TT::TypeTrackerContent;

  class ContentFilter = TT::ContentFilter;

  private predicate isLargeContentSet(Content cs) { strictcount(cs.getAReadContent()) > 10 }

  Content getLoadKey(Content loadSet) {
    if isLargeContentSet(loadSet)
    then result = loadSet // the corresponding store will have used the large ContentSet as the key
    else result.isSingleton(loadSet.getAReadContent())
  }

  Content getStoreKey(Content storeSet) {
    exists(DataFlow::Content content | content = storeSet.getAStoreContent() |
      isLargeContentSet(result) and
      result.getAReadContent() = content
      or
      result.isSingleton(content)
    )
  }

  pragma[nomagic]
  predicate storeStep(Node pred, Node succ, Content key) {
    exists(Content cs |
      TT::basicStoreStep(pred.getALocalUse(), succ.getALocalUse(), cs) and
      key = getStoreKey(cs)
    )
  }

  pragma[nomagic]
  predicate loadStep(Node pred, Node succ, Content key) {
    exists(Content cs |
      TT::basicLoadStep(pred.getALocalUse(), succ, cs) and
      key = getLoadKey(cs)
    )
  }

  pragma[nomagic]
  predicate loadStoreStep(Node pred, Node succ, Content loadKey, Content storeKey) {
    exists(Content loadSet, Content storeSet |
      TT::basicLoadStoreStep(pred.getALocalUse(), succ.getALocalUse(), loadSet, storeSet) and
      loadKey = getLoadKey(loadSet) and
      storeKey = getStoreKey(storeSet)
    )
  }

  predicate levelStep(Node pred, Node succ) {
    TT::levelStepCall(pred.getALocalUse(), succ)
    or
    TT::levelStepNoCall(pred.getALocalUse(), succ)
    or
    pred.flowsTo(succ) and
    pred != succ
  }

  predicate callStep(Node pred, Node succ) {
    TT::callStep(pred.getALocalUse(), succ) and
    not isSelfParameter(succ)
  }

  predicate withContentStep(Node pred, Node succ, TT::ContentFilter filter) {
    TT::basicWithContentStep(pred.getALocalUse(), succ, filter)
  }

  predicate withoutContentStep(Node pred, Node succ, TT::ContentFilter filter) {
    TT::basicWithoutContentStep(pred.getALocalUse(), succ, filter)
  }

  predicate returnStep(Node pred, Node succ) { TT::returnStep(pred.getALocalUse(), succ) }

  predicate jumpStep(Node pred, Node succ) { TT::jumpStep(pred.getALocalUse(), succ) }

  predicate isParameterLike(Node node) {
    node instanceof DataFlow::ParameterNode
    or
    node = Private::LocalFlow::getParameterDefNode(_)
  }

  predicate isSelfParameter(Node node) { node = any(DataFlow::CallableNode cn).getSelfParameter() }

  predicate shouldTrack(Node node) { any() }
}

module UniversalTypeTracking = UniversalTypeTrackingGen<UniversalTypeTrackingForRuby>;

module ConsistencyChecks {
  private import UniversalTypeTracking
  private import UniversalTypeTrackingForRuby

  private predicate matchingStoreLoad(Content storeSet, Content loadSet) {
    storeSet.getAStoreContent() = loadSet.getAReadContent()
  }

  /**
   * Holds if the matching of `storeSet` and `loadSet` does not hold
   * when using `getStoreKey` and `getLoadKey`.
   */
  query predicate contentSetsMatch(Content storeSet, Content loadSet, string diff) {
    matchingStoreLoad(storeSet, loadSet) and
    not getStoreKey(storeSet) = getLoadKey(loadSet) and
    diff = "missed match"
    or
    not matchingStoreLoad(storeSet, loadSet) and
    getStoreKey(storeSet) = getLoadKey(loadSet) and
    diff = "spurious match"
  }

  query predicate contentFiltersMatch(ContentFilter filter, Content contents, string diff) {
    exists(Content storeKey | storeKey = getStoreKey(contents) |
      filter.getAMatchingContent() = contents and
      not filter.getAMatchingContent() = storeKey and
      diff = "missed filter match"
      or
      not filter.getAMatchingContent() = contents and
      filter.getAMatchingContent() = storeKey and
      diff = "spurious filter match"
    )
  }

  private import codeql.ruby.typetracking.TypeTracker as T

  /** Gets a data flow node referring to a thing. */
  private Node trackReturnValue(T::TypeTracker t, DataFlow::CallNode call) {
    t.start() and
    result = call
    or
    exists(T::TypeTracker t2 |
      result = trackReturnValue(t2, call).track(t2, t) and
      not isSelfParameter(result)
    )
  }

  /** Gets a data flow node referring to a thing. */
  Node trackReturnValue(DataFlow::CallNode call) {
    result = trackReturnValue(T::TypeTracker::end(), call)
  }

  predicate diffFlow(DataFlow::CallNode call, Node to, string diff) {
    to = trackReturnValue(call) and
    not trackNode(call) = to and
    diff = "lost"
    or
    trackNode(call) = to and
    not trackReturnValue(call) = to and
    diff = "gained"
  }
}
