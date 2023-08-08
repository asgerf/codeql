private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.StepSummary
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps

module Private {
  private import Public

  newtype TReturnKind =
    MkNormalReturn() or
    MkExceptionalReturn()

  class ReturnKind extends TReturnKind {
    string toString() {
      this = MkNormalReturn() and result = "normal return"
      or
      this = MkExceptionalReturn() and result = "exceptional return"
    }
  }

  private class TReturnNode = TFunctionReturnNode or TExceptionalFunctionReturnNode;

  class ReturnNode extends DataFlow::Node, TReturnNode {
    ReturnKind getKind() {
      this instanceof TFunctionReturnNode and result = MkNormalReturn()
      or
      this instanceof TExceptionalFunctionReturnNode and result = MkExceptionalReturn()
    }
  }

  class OutNode extends DataFlow::Node {
    OutNode() {
      this instanceof DataFlow::InvokeNode
      or
      this instanceof TExceptionalInvocationReturnNode
    }
  }

  OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) {
    kind = MkNormalReturn() and result = call.asOrdinaryCall()
    or
    kind = MkExceptionalReturn() and result = call.asOrdinaryCall().getExceptionalReturn()
    or
    kind = MkNormalReturn() and result = call.asBoundCall(_)
    or
    kind = MkExceptionalReturn() and result = call.asBoundCall(_).getExceptionalReturn()
  }

  /**
   * Base class for classes that should be empty.
   */
  abstract private class EmptyType extends DataFlow::Node { }

  class PostUpdateNode extends DataFlow::Node instanceof EmptyType {
    DataFlow::Node getPreUpdateNode() { none() }
  }

  class CastNode extends DataFlow::Node instanceof EmptyType { }

  class DataFlowCallable = StmtContainer;

  predicate isParameterNode(Node p, DataFlowCallable c, ParameterPosition pos) {
    p = c.(Function).getParameter(pos).flow()
    or
    pos = -1 and p = TThisNode(c) and c instanceof Function
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
  }

  DataFlowCallable nodeGetEnclosingCallable(Node node) { result = node.getContainer() }

  class DataFlowType = Unit;

  DataFlowType getNodeType(Node node) { any() }

  predicate nodeIsHidden(Node node) { DataFlow::PathNode::shouldNodeBeHidden(node) }

  string ppReprType(DataFlowType t) { none() }

  pragma[inline]
  predicate compatibleTypes(DataFlowType t1, DataFlowType t2) { any() }

  class Content extends PropertyName { }

  predicate forceHighPrecision(Content c) { none() }

  class ContentApprox extends Content { }

  pragma[inline]
  ContentApprox getContentApprox(Content c) { result = c }

  private newtype TDataFlowCall =
    MkOrdinaryCall(DataFlow::InvokeNode node) or
    MkPartialCall(DataFlow::PartialInvokeNode node) or
    MkBoundCall(DataFlow::InvokeNode node, int boundArgs) {
      FlowSteps::callsBound(node, _, boundArgs)
    }

  class DataFlowCall extends TDataFlowCall {
    DataFlowCallable getEnclosingCallable() { none() } // Overridden in subclass

    string toString() { none() } // Overridden in subclass

    DataFlow::InvokeNode asOrdinaryCall() { this = MkOrdinaryCall(result) }

    DataFlow::PartialInvokeNode asPartialCall() { this = MkPartialCall(result) }

    DataFlow::InvokeNode asBoundCall(int boundArgs) { this = MkBoundCall(result, boundArgs) }
  }

  private class OrdinaryCall extends DataFlowCall, MkOrdinaryCall {
    private DataFlow::InvokeNode node;

    OrdinaryCall() { this = MkOrdinaryCall(node) }

    DataFlow::InvokeNode getNode() { result = node }

    override DataFlowCallable getEnclosingCallable() { result = node.getContainer() }

    override string toString() { result = node.toString() }
  }

  private class PartialCall extends DataFlowCall, MkPartialCall {
    private DataFlow::PartialInvokeNode node;

    PartialCall() { this = MkPartialCall(node) }

    DataFlow::PartialInvokeNode getNode() { result = node }

    override DataFlowCallable getEnclosingCallable() { result = node.getContainer() }

    override string toString() { result = node.toString() + " (as partial invocation)" }
  }

  private class BoundCall extends DataFlowCall, MkBoundCall {
    private DataFlow::InvokeNode node;
    private int boundArgs;

    BoundCall() { this = MkBoundCall(node, boundArgs) }

    override DataFlowCallable getEnclosingCallable() { result = node.getContainer() }

    override string toString() {
      result = node.toString() + " (as call with " + boundArgs + " bound arguments)"
    }
  }

  class ParameterPosition = int;

  class ArgumentPosition = int;

  class DataFlowExpr = Expr;

  predicate exprNode = DataFlow::exprNode/1;

  bindingset[apos]
  bindingset[ppos]
  pragma[inline]
  predicate parameterMatch(ParameterPosition ppos, ArgumentPosition apos) { ppos = apos }

  pragma[inline]
  Function viableCallable(DataFlowCall node) {
    result = node.asOrdinaryCall().getACallee()
    or
    result = node.asPartialCall().getACallbackNode().getAFunctionValue().getFunction()
    or
    exists(DataFlow::InvokeNode invoke, int boundArgs |
      invoke = node.asBoundCall(boundArgs) and
      FlowSteps::callsBound(invoke, result, boundArgs)
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
  }

  predicate simpleLocalFlowStep(Node node1, Node node2) {
    valuePreservingStep(node1, node2) and
    pragma[only_bind_out](node1).getContainer() = pragma[only_bind_out](node2).getContainer()
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a non-local step
   * that does not follow a call edge. For example, a step through a global
   * variable.
   */
  predicate jumpStep(Node node1, Node node2) {
    valuePreservingStep(node1, node2) and
    node1.getContainer() != node2.getContainer()
  }

  /**
   * Holds if data can flow from `node1` to `node2` via a read of `c`.  Thus,
   * `node1` references an object with a content `c.getAReadContent()` whose
   * value ends up in `node2`.
   */
  predicate readStep(Node node1, ContentSet c, Node node2) {
    exists(DataFlow::PropRead read |
      node1 = read.getBase() and
      c = read.getPropertyName() and
      node2 = read
    )
    or
    DataFlow::SharedFlowStep::loadStep(node1, node2, c)
  }

  /**
   * Holds if data can flow from `node1` to `node2` via a store into `c`.  Thus,
   * `node2` references an object with a content `c.getAStoreContent()` that
   * contains the value of `node1`.
   */
  predicate storeStep(Node node1, ContentSet c, Node node2) {
    exists(DataFlow::PropWrite write |
      node1 = write.getRhs() and
      c = write.getPropertyName() and
      node2 = write.getBase().getALocalSource() // TODO
    )
    or
    DataFlow::SharedFlowStep::storeStep(node1, node2, c)
  }

  /**
   * Holds if values stored inside content `c` are cleared at node `n`. For example,
   * any value stored inside `f` is cleared at the pre-update node associated with `x`
   * in `x.f = newValue`.
   */
  predicate clearsContent(Node n, ContentSet c) { none() }

  /**
   * Holds if the value that is being tracked is expected to be stored inside content `c`
   * at node `n`.
   */
  predicate expectsContent(Node n, ContentSet c) { none() }

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
  predicate lambdaCreation(Node creation, LambdaCallKind kind, DataFlowCallable c) { none() }

  /** Holds if `call` is a lambda call of kind `kind` where `receiver` is the lambda expression. */
  predicate lambdaCall(DataFlowCall call, LambdaCallKind kind, Node receiver) { none() }

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

  // TODO stub
  predicate defaultAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    TaintTracking::sharedTaintStep(pred, succ)
  }
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
  class ContentSet extends Private::Content {
    /** Gets a content that may be stored into when storing into this set. */
    pragma[inline]
    Private::Content getAStoreContent() { result = this }

    /** Gets a content that may be read from when reading from this set. */
    pragma[inline]
    Private::Content getAReadContent() { result = this }
  }
}
