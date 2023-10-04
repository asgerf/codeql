private import javascript
private import semmle.javascript.dataflow.internal.CallGraphs
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import semmle.javascript.dataflow.internal.Contents::Private
private import semmle.javascript.dataflow.internal.VariableCapture
private import semmle.javascript.dataflow.internal.sharedlib.DataFlowImplCommon as DataFlowImplCommon

private class Node = DataFlow::Node;

cached
newtype TReturnKind =
  MkNormalReturnKind() or
  MkExceptionalReturnKind()

class ReturnKind extends TReturnKind {
  string toString() {
    this = MkNormalReturnKind() and result = "return"
    or
    this = MkExceptionalReturnKind() and result = "exception"
  }
}

private predicate returnNodeImpl(DataFlow::Node node, ReturnKind kind) {
  node instanceof TFunctionReturnNode and kind = MkNormalReturnKind()
  or
  exists(Function fun |
    node = TExceptionalFunctionReturnNode(fun) and
    kind = MkExceptionalReturnKind() and
    // For async/generators, the exception is caught and wrapped in the returned promise/iterator object.
    // See the models for AsyncAwait and Generator.
    not fun.isAsyncOrGenerator()
  )
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
  kind = MkNormalReturnKind() and result = call.asAccessorCall().(DataFlow::PropRead)
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

cached
private predicate postUpdatePair(Node pre, Node post) {
  exists(AST::ValueNode expr |
    pre = TValueNode(expr) and
    post = TExprPostUpdateNode(expr)
  )
  or
  exists(NewExpr expr |
    pre = TConstructorThisArgumentNode(expr) and
    post = TValueNode(expr)
  )
  or
  exists(SuperCall expr |
    pre = TConstructorThisArgumentNode(expr) and
    post = TConstructorThisPostUpdate(expr.getBinder())
  )
  or
  exists(Function constructor |
    pre = TThisNode(constructor) and
    post = TConstructorThisPostUpdate(constructor)
  )
}

class PostUpdateNode extends DataFlow::Node {
  PostUpdateNode() { postUpdatePair(_, this) }

  final DataFlow::Node getPreUpdateNode() { postUpdatePair(result, this) }
}

class CastNode extends DataFlow::Node instanceof EmptyType { }

cached
newtype TDataFlowCallable =
  MkSourceCallable(StmtContainer container) or

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

  /** Gets the corresponding `StmtContainer` if this is a source callable. */
  pragma[nomagic]
  StmtContainer asSourceCallableNotExterns() {
    this = MkSourceCallable(result) and
    not result.inExternsFile()
  }

  /** Gets the corresponding `LibraryCallable` if this is a library callable. */
  LibraryCallable asLibraryCallable() { this = MkLibraryCallable(result) }
}

private predicate isParameterNodeImpl(Node p, DataFlowCallable c, ParameterPosition pos) {
  p = c.asSourceCallable().(Function).getParameter(pos.asPositional()).flow()
  or
  pos.isThis() and p = TThisNode(c.asSourceCallable().(Function))
  or
  pos.isFunctionSelfReference() and p = TFunctionSelfReferenceNode(c.asSourceCallable())
  or
  pos.isArgumentsArray() and p = TReflectiveParametersNode(c.asSourceCallable())
}

predicate isParameterNode(ParameterNode p, DataFlowCallable c, ParameterPosition pos) {
  isParameterNodeImpl(p, c, pos)
}

private predicate isArgumentNodeImpl(Node n, DataFlowCall call, ArgumentPosition pos) {
  n = call.asOrdinaryCall().getArgument(pos.asPositional())
  or
  pos.isThis() and n = call.asOrdinaryCall().(DataFlow::CallNode).getReceiver()
  or
  exists(DataFlow::PartialInvokeNode invoke, DataFlow::Node callback |
    call = MkPartialCall(invoke, callback) and
    invoke.isPartialArgument(callback, n, pos.asPositional())
  )
  or
  pos.isThis() and n = call.asPartialCall().getBoundReceiver()
  or
  exists(int boundArgs |
    n = call.asBoundCall(boundArgs).getArgument(pos.asPositional() - boundArgs)
  )
  or
  pos.isThis() and n = TConstructorThisArgumentNode(call.asOrdinaryCall().asExpr())
  or
  // For now, treat all spread argument as flowing into the 'arguments' array, regardless of preceding arguments
  n = call.asOrdinaryCall().getASpreadArgument() and
  pos.isArgumentsArray()
  or
  // receiver of accessor call
  pos.isThis() and n = call.asAccessorCall().getBase()
  or
  // argument to setter (TODO: this has no post-update node)
  pos.asPositional() = 0 and n = call.asAccessorCall().(DataFlow::PropWrite).getRhs()
}

predicate isArgumentNode(ArgumentNode n, DataFlowCall call, ArgumentPosition pos) {
  isArgumentNodeImpl(n, call, pos)
}

DataFlowCallable nodeGetEnclosingCallable(Node node) {
  result.asSourceCallable() = node.getContainer()
}

private newtype TDataFlowType =
  TTodoDataFlowType() or
  TTodoDataFlowType2() // Add a dummy value to prevent bad functionality-induced joins arising from a type of size 1.

class DataFlowType extends TDataFlowType {
  string toString() { result = "" }
}

predicate typeStrongerThan(DataFlowType t1, DataFlowType t2) { none() }

DataFlowType getNodeType(Node node) { result = TTodoDataFlowType() and exists(node) }

predicate nodeIsHidden(Node node) {
  DataFlow::PathNode::shouldNodeBeHidden(node)
}

predicate neverSkipInPathGraph(Node node) {
  // Include the left-hand side of assignments
  node = DataFlow::lvalueNode(_)
  or
  // Include the return-value expression
  node.asExpr() = any(Function f).getAReturnedExpr()
  or
  // Include calls (which may have been modelled as steps)
  node.asExpr() instanceof InvokeExpr
  or
  // Include references to a variable
  node.asExpr() instanceof VarRef
}

string ppReprType(DataFlowType t) { none() }

pragma[inline]
predicate compatibleTypes(DataFlowType t1, DataFlowType t2) { any() }

predicate forceHighPrecision(Content c) { none() }

class ContentApprox extends Content { }

pragma[inline]
ContentApprox getContentApprox(Content c) { result = c }

cached
private newtype TDataFlowCall =
  MkOrdinaryCall(DataFlow::InvokeNode node) or
  MkPartialCall(DataFlow::PartialInvokeNode node, DataFlow::Node callback) {
    callback = node.getACallbackNode()
  } or
  MkBoundCall(DataFlow::InvokeNode node, int boundArgs) {
    FlowSteps::callsBound(node, _, boundArgs)
  } or
  MkAccessorCall(DataFlow::PropRef node) {
    // Some PropRefs can't result in an accessor call, such as Object.defineProperty.
    // Restrict to PropRefs that can result in an accessor call.
    node = TValueNode(any(PropAccess p)) or
    node = TPropNode(any(PropertyPattern p))
  } or

class DataFlowCall extends TDataFlowCall {
  DataFlowCallable getEnclosingCallable() { none() } // Overridden in subclass

  string toString() { none() } // Overridden in subclass

  DataFlow::InvokeNode asOrdinaryCall() { this = MkOrdinaryCall(result) }

  DataFlow::PropRef asAccessorCall() { this = MkAccessorCall(result) }

  DataFlow::PartialInvokeNode asPartialCall() { this = MkPartialCall(result, _) }

  DataFlow::InvokeNode asBoundCall(int boundArgs) { this = MkBoundCall(result, boundArgs) }

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
  private DataFlow::Node callback;

  PartialCall() { this = MkPartialCall(node, callback) }

  DataFlow::PartialInvokeNode getNode() { result = node }

  DataFlow::Node getCallback() { result = callback }

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

private class AccessorCall extends DataFlowCall, MkAccessorCall {
  private DataFlow::PropRef ref;

  AccessorCall() { this = MkAccessorCall(ref) }

  override DataFlowCallable getEnclosingCallable() {
    result.asSourceCallable() = ref.getContainer()
  }

  override string toString() { result = ref.toString() + " (as accessor call)" }

  override predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    ref.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
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

cached
newtype TParameterPosition =
  MkPositionalParameter(int n) { n = [0 .. getMaxArity()] } or
  MkPositionalLowerBound(int n) { n = [0 .. getMaxArity()] } or
  MkThisParameter() or
  MkArgumentsArrayParameter()

class ParameterPosition extends TParameterPosition {
  predicate isPositionalExact() { this instanceof MkPositionalParameter }

  predicate isPositionalLowerBound() { this instanceof MkPositionalLowerBound }

  predicate isPositionalLike() { this.isPositionalExact() or this.isPositionalLowerBound() }

  int asPositional() { this = MkPositionalParameter(result) }

  int asPositionalLowerBound() { this = MkPositionalLowerBound(result) }

  predicate isThis() { this = MkThisParameter() }

  predicate isArgumentsArray() { this = MkArgumentsArrayParameter() }

  string toString() {
    result = this.asPositional().toString()
    or
    result = this.asPositionalLowerBound().toString() + ".."
    or
    this.isThis() and result = "this"
    or
    this.isArgumentsArray() and result = "arguments-array"
  }
}

class ArgumentPosition extends ParameterPosition { }

class DataFlowExpr = Expr;

Node exprNode(DataFlowExpr expr) { result = DataFlow::exprNode(expr) }

pragma[nomagic]
predicate parameterMatch(ParameterPosition ppos, ArgumentPosition apos) {
  ppos = apos
  or
  apos.asPositional() >= ppos.asPositionalLowerBound()
  or
  ppos.asPositional() >= apos.asPositionalLowerBound()
  //
  // Note: for now, there is no need to match lower bounds agaist lower bounds since we
  // are only using these in cases where either the call or callee is generated by a flow summary.
}

pragma[inline]
DataFlowCallable viableCallable(DataFlowCall node) {
  // Note: we never include call edges externs here, as it negatively affects the field-flow branch limit,
  // particularly when the call can also target a flow summary.
  result.asSourceCallableNotExterns() = node.asOrdinaryCall().getACallee()
  or
  result.asSourceCallableNotExterns() =
    node.(PartialCall).getCallback().getAFunctionValue().getFunction()
  or
  exists(DataFlow::InvokeNode invoke, int boundArgs |
    invoke = node.asBoundCall(boundArgs) and
    FlowSteps::callsBound(invoke, result.asSourceCallableNotExterns(), boundArgs)
  )
  or
  result.asSourceCallableNotExterns() = node.asAccessorCall().getAnAccessorCallee().getFunction()
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

bindingset[node1, node2]
pragma[inline_late]
private predicate sameContainer(Node node1, Node node2) {
  node1.getContainer() = node2.getContainer()
}

bindingset[node, fun]
pragma[inline_late]
private predicate sameContainerAsEnclosingContainer(Node node, Function fun) {
  node.getContainer() = fun.getEnclosingContainer()
}

/**
 * Holds if there is a value-preserving steps `node1` -> `node2` that might
 * be cross function boundaries.
 */
private predicate valuePreservingStep(Node node1, Node node2) {
  node1.getASuccessor() = node2 and
  or
  FlowSteps::propertyFlowStep(node1, node2)
  or
  FlowSteps::globalFlowStep(node1, node2)
  or
  node2 = FlowSteps::getThrowTarget(node1)
  or
  // Step from post-update nodes to local sources of the pre-update node. This emulates how JS usually tracks side effects.
  exists(PostUpdateNode postUpdate |
    node1 = postUpdate and
    node2 = postUpdate.getPreUpdateNode().getALocalSource() and
    node1 != node2 and // exclude trivial edges
    sameContainer(node1, node2)
  )
}

predicate simpleLocalFlowStep(Node node1, Node node2) {
  valuePreservingStep(node1, node2) and
  nodeGetEnclosingCallable(pragma[only_bind_out](node1)) =
    nodeGetEnclosingCallable(pragma[only_bind_out](node2))
}

predicate localMustFlowStep(Node node1, Node node2) { node1 = node2.getImmediatePredecessor() }

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
    node2 = read
  |
    c.asPropertyName() = read.getPropertyName()
    or
    not exists(read.getPropertyName()) and
    c = ContentSet::arrayElement()
  )
}

/** Gets the post-update node for which `node` is the corresponding pre-update node. */
private Node getPostUpdate(Node node) { result.(PostUpdateNode).getPreUpdateNode() = node }

/** Gets the post-update node for which node is the pre-update node, if one exists, otherwise gets `node` itself. */
pragma[inline]
private Node tryGetPostUpdate(Node node) {
  result = getPostUpdate(node)
  or
  not exists(getPostUpdate(node)) and
  result = node
}

/**
 * Holds if data can flow from `node1` to `node2` via a store into `c`.  Thus,
 * `node2` references an object with a content `c.getAStoreContent()` that
 * contains the value of `node1`.
 */
predicate storeStep(Node node1, ContentSet c, Node node2) {
  exists(DataFlow::PropWrite write |
    node1 = write.getRhs() and
    c.asPropertyName() = write.getPropertyName() and
    // Target the post-update node if one exists (for object literals we do not generate post-update nodes)
    node2 = tryGetPostUpdate(write.getBase())
  )
}

/**
 * Holds if values stored inside content `c` are cleared at node `n`. For example,
 * any value stored inside `f` is cleared at the pre-update node associated with `x`
 * in `x.f = newValue`.
 */
predicate clearsContent(Node n, ContentSet c) {
}

/**
 * Holds if the value that is being tracked is expected to be stored inside content `c`
 * at node `n`.
 */
predicate expectsContent(Node n, ContentSet c) {
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
predicate allowParameterReturnInSelf(ParameterNode p) {
}

class LambdaCallKind = Unit; // TODO: not sure about this

/** Holds if `creation` is an expression that creates a lambda of kind `kind` for `c`. */
predicate lambdaCreation(Node creation, LambdaCallKind kind, DataFlowCallable c) {
  creation.(DataFlow::FunctionNode).getFunction() = c.asSourceCallable() and exists(kind)
}

/** Holds if `call` is a lambda call of kind `kind` where `receiver` is the lambda expression. */
predicate lambdaCall(DataFlowCall call, LambdaCallKind kind, Node receiver) {
  receiver = call.asOrdinaryCall().getCalleeNode() and exists(kind)
}

/** Extra data-flow steps needed for lambda flow analysis. */
predicate additionalLambdaFlowStep(Node nodeFrom, Node nodeTo, boolean preservesValue) { none() }

class ArgumentNode extends DataFlow::Node {
  ArgumentNode() { isArgumentNodeImpl(this, _, _) }

  predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
    isArgumentNodeImpl(this, call, pos)
  }
}

class ParameterNode extends DataFlow::Node {
  ParameterNode() { isParameterNodeImpl(this, _, _) }
}
