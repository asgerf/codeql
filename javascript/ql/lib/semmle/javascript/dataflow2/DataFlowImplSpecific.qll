private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.StepSummary
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import FlowSummaryImpl as FlowSummaryImpl

module Private {
  private import Public

  class FlowSummaryNode extends DataFlow::Node, TFlowSummaryNode {
    FlowSummaryImpl::Private::SummaryNode getSummaryNode() { this = TFlowSummaryNode(result) }

    /** Gets the summarized callable that this node belongs to. */
    FlowSummaryImpl::Public::SummarizedCallable getSummarizedCallable() {
      result = this.getSummaryNode().getSummarizedCallable()
    }

    override string toString() { result = this.getSummaryNode().toString() }
  }

  newtype TReturnKind =
    MkNormalReturnKind() or
    MkExceptionalReturnKind()

  class ReturnKind extends TReturnKind {
    string toString() {
      this = MkNormalReturnKind() and result = "normal return"
      or
      this = MkExceptionalReturnKind() and result = "exceptional return"
    }
  }

  private predicate returnNodeImpl(DataFlow::Node node, ReturnKind kind) {
    node instanceof TFunctionReturnNode and kind = MkNormalReturnKind()
    or
    node instanceof TExceptionalFunctionReturnNode and kind = MkExceptionalReturnKind()
    or
    FlowSummaryImpl::Private::summaryReturnNode(node.(FlowSummaryNode).getSummaryNode(), kind)
  }

  private DataFlow::Node getAnOutNodeImpl(DataFlowCall call, ReturnKind kind) {
    kind = MkNormalReturnKind() and result = call.asOrdinaryCall()
    or
    kind = MkExceptionalReturnKind() and result = call.asOrdinaryCall().getExceptionalReturn()
    or
    kind = MkNormalReturnKind() and result = call.asBoundCall(_)
    or
    kind = MkExceptionalReturnKind() and result = call.asBoundCall(_).getExceptionalReturn()
    or
    FlowSummaryImpl::Private::summaryOutNode(call, result.(FlowSummaryNode).getSummaryNode(), kind)
  }

  class ReturnNode extends DataFlow::Node {
    ReturnNode() { returnNodeImpl(this, _) }

    ReturnKind getKind() { returnNodeImpl(this, result) }
  }

  /** A node that receives an output from a call. */
  class OutNode extends DataFlow::Node {
    OutNode() { this = getAnOutNodeImpl(_, _) }
  }

  OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) { result = getAnOutNodeImpl(call, kind) }

  /**
   * Base class for classes that should be empty.
   */
  abstract private class EmptyType extends DataFlow::Node { }

  class PostUpdateNode extends DataFlow::Node instanceof EmptyType {
    DataFlow::Node getPreUpdateNode() { none() }
  }

  class CastNode extends DataFlow::Node instanceof EmptyType { }

  newtype TDataFlowCallable =
    MkSourceCallable(StmtContainer container) or
    MkLibraryCallable(LibraryCallable callable)

  /**
   * A callable entity. This is a wrapper around either a `StmtContainer` or a `LibraryCallable`.
   */
  class DataFlowCallable extends TDataFlowCallable {
    /** Gets a string representation of this callable. */
    string toString() {
      result = this.asSourceCallable().toString()
      or
      result = this.asLibraryCallable()
    }

    /** Gets the location of this callable, if it is present in the source code. */
    Location getLocation() { result = this.asSourceCallable().getLocation() }

    /** Gets the corresponding `StmtContainer` if this is a source callable. */
    StmtContainer asSourceCallable() { this = MkSourceCallable(result) }

    /** Gets the corresponding `LibraryCallable` if this is a library callable. */
    LibraryCallable asLibraryCallable() { this = MkLibraryCallable(result) }
  }

  /** A callable defined in library code, identified by a unique string. */
  abstract class LibraryCallable extends string {
    bindingset[this]
    LibraryCallable() { any() }

    /** Gets a call to this library callable. */
    DataFlow::InvokeNode getACall() { none() }

    /** Same as `getACall()` except this does not depend on the call graph or API graph. */
    DataFlow::InvokeNode getACallSimple() { none() }
  }

  predicate isParameterNode(Node p, DataFlowCallable c, ParameterPosition pos) {
    p = c.asSourceCallable().(Function).getParameter(pos).flow()
    or
    pos = -1 and p = TThisNode(c.asSourceCallable().(Function))
    or
    exists(FlowSummaryNode summaryNode |
      summaryNode = p and
      FlowSummaryImpl::Private::summaryParameterNode(summaryNode.getSummaryNode(), pos) and
      c.asLibraryCallable() = summaryNode.getSummarizedCallable()
    )
  }

  predicate isArgumentNode(Node n, DataFlowCall call, ArgumentPosition pos) {
    n = call.asOrdinaryCall().getArgument(pos)
    or
    pos = -1 and n = call.asOrdinaryCall().(DataFlow::CallNode).getReceiver()
    or
    call.asPartialCall().isPartialArgument(_, n, pos)
    or
    pos = -1 and n = call.asPartialCall().getBoundReceiver()
    or
    exists(int boundArgs | n = call.asBoundCall(boundArgs).getArgument(pos - boundArgs))
    or
    FlowSummaryImpl::Private::summaryArgumentNode(call, n.(FlowSummaryNode).getSummaryNode(), pos)
  }

  DataFlowCallable nodeGetEnclosingCallable(Node node) {
    result.asSourceCallable() = node.getContainer()
    or
    result.asLibraryCallable() = node.(FlowSummaryNode).getSummarizedCallable()
  }

  private newtype TDataFlowType =
    TTodoDataFlowType() or
    TTodoDataFlowType2() // Add a dummy value to prevent bad functionality-induced joins arising from a type of size 1.

  class DataFlowType extends TDataFlowType {
    string toString() { result = "" }
  }

  DataFlowType getNodeType(Node node) { result = TTodoDataFlowType() and exists(node) }

  predicate nodeIsHidden(Node node) {
    DataFlow::PathNode::shouldNodeBeHidden(node)
    or
    node instanceof FlowSummaryNode
  }

  string ppReprType(DataFlowType t) { none() }

  pragma[inline]
  predicate compatibleTypes(DataFlowType t1, DataFlowType t2) { any() }

  class Content extends string {
    Content() {
      this = any(PropAccess access).getPropertyName()
      or
      this = any(PropertyPattern p).getName()
      or
      this = any(GlobalVariable v).getName()
      or
      this =
        [
          DataFlow::PseudoProperties::arrayElement(), DataFlow::PseudoProperties::mapValueAll(),
          Promises::valueProp(), Promises::errorProp()
        ]
    }
  }

  predicate forceHighPrecision(Content c) { none() }

  class ContentApprox extends Content { }

  pragma[inline]
  ContentApprox getContentApprox(Content c) { result = c }

  private newtype TDataFlowCall =
    MkOrdinaryCall(DataFlow::InvokeNode node) or
    MkPartialCall(DataFlow::PartialInvokeNode node) or
    MkBoundCall(DataFlow::InvokeNode node, int boundArgs) {
      FlowSteps::callsBound(node, _, boundArgs)
    } or
    MkSummaryCall(
      FlowSummaryImpl::Public::SummarizedCallable c, FlowSummaryImpl::Private::SummaryNode receiver
    ) {
      FlowSummaryImpl::Private::summaryCallbackRange(c, receiver)
    }

  class DataFlowCall extends TDataFlowCall {
    DataFlowCallable getEnclosingCallable() { none() } // Overridden in subclass

    string toString() { none() } // Overridden in subclass

    DataFlow::InvokeNode asOrdinaryCall() { this = MkOrdinaryCall(result) }

    DataFlow::PartialInvokeNode asPartialCall() { this = MkPartialCall(result) }

    DataFlow::InvokeNode asBoundCall(int boundArgs) { this = MkBoundCall(result, boundArgs) }

    predicate isSummaryCall(
      FlowSummaryImpl::Public::SummarizedCallable enclosingCallable,
      FlowSummaryImpl::Private::SummaryNode receiver
    ) {
      this = MkSummaryCall(enclosingCallable, receiver)
    }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      none() // Overridden in subclass
    }
  }

  private class OrdinaryCall extends DataFlowCall, MkOrdinaryCall {
    private DataFlow::InvokeNode node;

    OrdinaryCall() { this = MkOrdinaryCall(node) }

    DataFlow::InvokeNode getNode() { result = node }

    override DataFlowCallable getEnclosingCallable() {
      result.asSourceCallable() = node.getContainer()
    }

    override string toString() { result = node.toString() }

    override predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      node.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

  private class PartialCall extends DataFlowCall, MkPartialCall {
    private DataFlow::PartialInvokeNode node;

    PartialCall() { this = MkPartialCall(node) }

    DataFlow::PartialInvokeNode getNode() { result = node }

    override DataFlowCallable getEnclosingCallable() {
      result.asSourceCallable() = node.getContainer()
    }

    override string toString() { result = node.toString() + " (as partial invocation)" }

    override predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      node.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

  private class BoundCall extends DataFlowCall, MkBoundCall {
    private DataFlow::InvokeNode node;
    private int boundArgs;

    BoundCall() { this = MkBoundCall(node, boundArgs) }

    override DataFlowCallable getEnclosingCallable() {
      result.asSourceCallable() = node.getContainer()
    }

    override string toString() {
      result = node.toString() + " (as call with " + boundArgs + " bound arguments)"
    }

    override predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      node.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

  class SummaryCall extends DataFlowCall, MkSummaryCall {
    private FlowSummaryImpl::Public::SummarizedCallable enclosingCallable;
    private FlowSummaryImpl::Private::SummaryNode receiver;

    SummaryCall() { this = MkSummaryCall(enclosingCallable, receiver) }

    override DataFlowCallable getEnclosingCallable() {
      result.asLibraryCallable() = enclosingCallable
    }

    override string toString() {
      result = "[summary] call to " + receiver + " in " + enclosingCallable
    }

    /** Gets the receiver node. */
    FlowSummaryImpl::Private::SummaryNode getReceiver() { result = receiver }
  }

  private int getMaxArity() {
    // TODO: account for flow summaries
    result =
      max(int n |
        n = any(InvokeExpr e).getNumArgument() or
        n = any(Function f).getNumParameter() or
        n = 10
      )
  }

  class ParameterPosition extends int {
    ParameterPosition() {
      this = [0 .. getMaxArity()]
      or
      this = -1 // receiver
    }
  }

  class ArgumentPosition extends int {
    ArgumentPosition() { this instanceof ParameterPosition }
  }

  class DataFlowExpr = Expr;

  predicate exprNode = DataFlow::exprNode/1;

  bindingset[apos]
  bindingset[ppos]
  pragma[inline]
  predicate parameterMatch(ParameterPosition ppos, ArgumentPosition apos) { ppos = apos }

  pragma[inline]
  DataFlowCallable viableCallable(DataFlowCall node) {
    result.asSourceCallable() = node.asOrdinaryCall().getACallee()
    or
    result.asSourceCallable() =
      node.asPartialCall().getACallbackNode().getAFunctionValue().getFunction()
    or
    exists(DataFlow::InvokeNode invoke, int boundArgs |
      invoke = node.asBoundCall(boundArgs) and
      FlowSteps::callsBound(invoke, result.asSourceCallable(), boundArgs)
    )
    or
    exists(LibraryCallable callable |
      result = MkLibraryCallable(callable) and
      node.asOrdinaryCall() = [callable.getACall(), callable.getACallSimple()]
    )
  }

  /**
   * Holds if the set of viable implementations that can be called by `call`
   * might be improved by knowing the call context.
   */
  predicate mayBenefitFromCallContext(DataFlowCall call, DataFlowCallable c) { none() }

  /**
   * Gets a viable dispatch target of `call` in the context `ctx`. This is
   * restricted to those `call`s for which a context might make a difference.
   */
  DataFlowCallable viableImplInCallContext(DataFlowCall call, DataFlowCall ctx) { none() }

  /**
   * Holds if there is a value-preserving steps `node1` -> `node2` that might
   * be cross function boundaries.
   */
  private predicate valuePreservingStep(Node node1, Node node2) {
    node1.getASuccessor() = node2
    or
    DataFlow::SharedFlowStep::step(node1, node2)
    or
    FlowSteps::propertyFlowStep(node1, node2)
    or
    FlowSteps::globalFlowStep(node1, node2)
    or
    FlowSteps::localExceptionStep(node1, node2)
    or
    FlowSummaryImpl::Private::Steps::summaryLocalStep(node1.(FlowSummaryNode).getSummaryNode(),
      node2.(FlowSummaryNode).getSummaryNode(), true)
    or
    exists(DataFlow::Node pred, DataFlow::Node succ, string prop |
      DataFlow::SharedFlowStep::loadStoreStep(pred, succ, prop)
    |
      node1 = pred and
      node2 = TSynthExpectPromiseNode(succ.asExpr(), prop)
      or
      node1 = TSynthExpectPromiseNode(succ.asExpr(), prop) and
      node2 = succ
    )
  }

  predicate simpleLocalFlowStep(Node node1, Node node2) {
    valuePreservingStep(node1, node2) and
    nodeGetEnclosingCallable(pragma[only_bind_out](node1)) =
      nodeGetEnclosingCallable(pragma[only_bind_out](node2))
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a non-local step
   * that does not follow a call edge. For example, a step through a global
   * variable.
   */
  predicate jumpStep(Node node1, Node node2) {
    valuePreservingStep(node1, node2) and
    node1.getContainer() != node2.getContainer()
    or
    FlowSummaryImpl::Private::Steps::summaryJumpStep(node1.(FlowSummaryNode).getSummaryNode(),
      node2.(FlowSummaryNode).getSummaryNode())
  }

  /**
   * Holds if data can flow from `node1` to `node2` via a read of `c`.  Thus,
   * `node1` references an object with a content `c.getAReadContent()` whose
   * value ends up in `node2`.
   */
  predicate readStep(Node node1, ContentSet c, Node node2) {
    exists(DataFlow::PropRead read |
      node1 = read.getBase() and
      c.asSingleton() = read.getPropertyName() and
      node2 = read
    )
    or
    DataFlow::SharedFlowStep::loadStep(node1, node2, c.asSingleton())
    or
    FlowSummaryImpl::Private::Steps::summaryReadStep(node1.(FlowSummaryNode).getSummaryNode(), c,
      node2.(FlowSummaryNode).getSummaryNode())
  }

  /**
   * Holds if data can flow from `node1` to `node2` via a store into `c`.  Thus,
   * `node2` references an object with a content `c.getAStoreContent()` that
   * contains the value of `node1`.
   */
  predicate storeStep(Node node1, ContentSet c, Node node2) {
    exists(DataFlow::PropWrite write |
      node1 = write.getRhs() and
      c.asSingleton() = write.getPropertyName() and
      node2 = write.getBase().getALocalSource() // TODO
    )
    or
    DataFlow::SharedFlowStep::storeStep(node1, node2, c.asSingleton())
    or
    FlowSummaryImpl::Private::Steps::summaryStoreStep(node1.(FlowSummaryNode).getSummaryNode(), c,
      node2.(FlowSummaryNode).getSummaryNode())
  }

  /**
   * Holds if values stored inside content `c` are cleared at node `n`. For example,
   * any value stored inside `f` is cleared at the pre-update node associated with `x`
   * in `x.f = newValue`.
   */
  predicate clearsContent(Node n, ContentSet c) {
    FlowSummaryImpl::Private::Steps::summaryClearsContent(n.(FlowSummaryNode).getSummaryNode(), c)
  }

  /**
   * Holds if the value that is being tracked is expected to be stored inside content `c`
   * at node `n`.
   */
  predicate expectsContent(Node n, ContentSet c) {
    n = TSynthExpectPromiseNode(_, c.asSingleton())
    or
    FlowSummaryImpl::Private::Steps::summaryExpectsContent(n.(FlowSummaryNode).getSummaryNode(), c)
  }

  /**
   * Holds if the node `n` is unreachable when the call context is `call`.
   */
  predicate isUnreachableInCall(Node n, DataFlowCall call) {
    none() // TODO: could be useful, but not currently implemented for JS
  }

  int accessPathLimit() { result = 5 }

  /**
   * Holds if flow is allowed to pass from parameter `p` and back to itself as a
   * side-effect, resulting in a summary from `p` to itself.
   *
   * One example would be to allow flow like `p.foo = p.bar;`, which is disallowed
   * by default as a heuristic.
   */
  // predicate allowParameterReturnInSelf(ParameterNode p);
  predicate allowParameterReturnInSelf(Node p) {
    none() // TODO: not sure what this means for JS
  }

  class LambdaCallKind = Unit; // TODO: not sure about this

  /** Holds if `creation` is an expression that creates a lambda of kind `kind` for `c`. */
  predicate lambdaCreation(Node creation, LambdaCallKind kind, DataFlowCallable c) {
    creation.(DataFlow::FunctionNode).getFunction() = c.asSourceCallable() and exists(kind)
  }

  /** Holds if `call` is a lambda call of kind `kind` where `receiver` is the lambda expression. */
  predicate lambdaCall(DataFlowCall call, LambdaCallKind kind, Node receiver) {
    call.isSummaryCall(_, receiver.(FlowSummaryNode).getSummaryNode()) and exists(kind)
  }

  /** Extra data-flow steps needed for lambda flow analysis. */
  predicate additionalLambdaFlowStep(Node nodeFrom, Node nodeTo, boolean preservesValue) { none() }

  /**
   * Gets an additional term that is added to the `join` and `branch` computations to reflect
   * an additional forward or backwards branching factor that is not taken into account
   * when calculating the (virtual) dispatch cost.
   *
   * Argument `arg` is part of a path from a source to a sink, and `p` is the target parameter.
   */
  int getAdditionalFlowIntoCallNodeTerm(Node arg, Node p) { none() }

  pragma[inline]
  predicate golangSpecificParamArgFilter(DataFlowCall call, Node p, Node arg) { any() }

  class ArgumentNode extends DataFlow::Node {
    ArgumentNode() { isArgumentNode(this, _, _) }

    predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
      isArgumentNode(this, call, pos)
    }
  }

  class ParameterNode extends DataFlow::Node {
    ParameterNode() { isParameterNode(this, _, _) }
  }

  predicate defaultAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    TaintTracking::sharedTaintStep(node1, node2)
    or
    FlowSummaryImpl::Private::Steps::summaryLocalStep(node1.(FlowSummaryNode).getSummaryNode(),
      node2.(FlowSummaryNode).getSummaryNode(), false)
    //
    // Note: the JS taint-tracking library has steps that treat store/read as taint steps in many cases,
    // e.g. pushing to an array taints the whole array, and a promise of a tainted value is itself considered tainted.
    // However, we never induce taint steps from store/read steps in flow summaries; instead there must be explicit
    // flow summaries with the corresponding taint steps (if desired).
  }

  newtype TContentSet = MkSingletonContent(Content content)
}

module Public {
  private import semmle.javascript.dataflow.DataFlow

  class Node = DataFlow::Node;

  /**
   * An entity that represents a set of `Content`s.
   *
   * The set may be interpreted differently depending on whether it is
   * stored into (`getAStoreContent`) or read from (`getAReadContent`).
   */
  class ContentSet extends Private::TContentSet {
    /** Gets a content that may be stored into when storing into this set. */
    pragma[inline]
    Private::Content getAStoreContent() { result = this.asSingleton() }

    /** Gets a content that may be read from when reading from this set. */
    pragma[inline]
    Private::Content getAReadContent() { result = this.asSingleton() }

    Private::Content asSingleton() { this = Private::MkSingletonContent(result) }

    string toString() { result = this.asSingleton() }
  }

  module ContentSet {
    pragma[inline]
    ContentSet singleton(Private::Content content) { result.asSingleton() = content }
  }
}
