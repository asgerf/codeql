private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.StepSummary
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import semmle.javascript.dataflow.internal.CallGraphs
private import semmle.javascript.dataflow2.AdditionalFlowInternal
private import FlowSummaryImpl as FlowSummaryImpl
private import semmle.javascript.internal.flow_summaries.AllFlowSummaries
private import VariableCaptureSpecific

module Private {
  private import Public

  int getMaxPreciseArrayIndex() { result = 9 }

  /** Gets an index which is tracked as a precise array index. */
  int getAPreciseArrayIndex() { result = [0 .. getMaxPreciseArrayIndex()] }

  class FlowSummaryNode extends DataFlow::Node, TFlowSummaryNode {
    FlowSummaryImpl::Private::SummaryNode getSummaryNode() { this = TFlowSummaryNode(result) }

    /** Gets the summarized callable that this node belongs to. */
    FlowSummaryImpl::Public::SummarizedCallable getSummarizedCallable() {
      result = this.getSummaryNode().getSummarizedCallable()
    }

    override string toString() { result = this.getSummaryNode().toString() }
  }

  class FlowSummaryIntermediateAwaitStoreNode extends DataFlow::Node,
    TFlowSummaryIntermediateAwaitStoreNode
  {
    FlowSummaryImpl::Private::SummaryNode getSummaryNode() {
      this = TFlowSummaryIntermediateAwaitStoreNode(result)
    }

    /** Gets the summarized callable that this node belongs to. */
    FlowSummaryImpl::Public::SummarizedCallable getSummarizedCallable() {
      result = this.getSummaryNode().getSummarizedCallable()
    }

    override string toString() {
      result = this.getSummaryNode().toString() + " [intermediate node for Awaited store]"
    }
  }

  class CaptureNode extends DataFlow::Node, TSynthCaptureNode {
    private VariableCaptureOutput::SynthesizedCaptureNode node;

    CaptureNode() { this = TSynthCaptureNode(node) }

    /** Gets the underlying node from the variable-capture library. */
    VariableCaptureOutput::SynthesizedCaptureNode getNode() { result = node }

    override StmtContainer getContainer() { result = node.getEnclosingCallable() }

    override string toString() { result = node.toString() }

    override predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      node.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

  class GenericSynthesizedNode extends DataFlow::Node, TGenericSynthesizedNode {
    private AstNode node;
    private string tag;
    private StmtContainer container;

    GenericSynthesizedNode() { this = TGenericSynthesizedNode(node, tag, container) }

    override StmtContainer getContainer() { result = container }

    override string toString() { result = "[synthetic node] " + tag }

    override predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      node.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

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
    kind = MkNormalReturnKind() and result = call.asAccessorCall().(DataFlow::PropRead)
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
    exists(SuperCall call |
      // Note: this step can cross function boundaries in absurd cases where super
      // appears in a closure. We ignore this corner case for now.
      pre = TConstructorThisArgumentNode(call) and
      post = TThisNode(call.getBinder())
    )
    or
    FlowSummaryImpl::Private::summaryPostUpdateNode(post.(FlowSummaryNode).getSummaryNode(),
      pre.(FlowSummaryNode).getSummaryNode())
    or
    VariableCaptureOutput::capturePostUpdateNode(getClosureNode(post), getClosureNode(pre))
  }

  class PostUpdateNode extends DataFlow::Node {
    PostUpdateNode() { postUpdatePair(_, this) }

    final DataFlow::Node getPreUpdateNode() { postUpdatePair(result, this) }
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

    /** Gets the corresponding `StmtContainer` if this is a source callable. */
    pragma[nomagic]
    StmtContainer asSourceCallableNotExterns() {
      this = MkSourceCallable(result) and
      not result.inExternsFile()
    }

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

  private predicate isParameterNodeImpl(Node p, DataFlowCallable c, ParameterPosition pos) {
    p = c.asSourceCallable().(Function).getParameter(pos.asPositional()).flow()
    or
    pos.isThis() and p = TThisNode(c.asSourceCallable().(Function))
    or
    pos.isFunctionSelfReference() and p = TFunctionSelfReferenceNode(c.asSourceCallable())
    or
    pos.isArgumentsArray() and p = TReflectiveParametersNode(c.asSourceCallable())
    or
    exists(FlowSummaryNode summaryNode |
      summaryNode = p and
      FlowSummaryImpl::Private::summaryParameterNode(summaryNode.getSummaryNode(), pos) and
      c.asLibraryCallable() = summaryNode.getSummarizedCallable()
    )
  }

  predicate isParameterNode(ParameterNode p, DataFlowCallable c, ParameterPosition pos) {
    isParameterNodeImpl(p, c, pos)
  }

  private predicate isArgumentNodeImpl(Node n, DataFlowCall call, ArgumentPosition pos) {
    n = call.asOrdinaryCall().getArgument(pos.asPositional())
    or
    pos.isThis() and n = call.asOrdinaryCall().(DataFlow::CallNode).getReceiver()
    or
    call.asPartialCall().isPartialArgument(_, n, pos.asPositional())
    or
    pos.isThis() and n = call.asPartialCall().getBoundReceiver()
    or
    exists(int boundArgs |
      n = call.asBoundCall(boundArgs).getArgument(pos.asPositional() - boundArgs)
    )
    or
    FlowSummaryImpl::Private::summaryArgumentNode(call, n.(FlowSummaryNode).getSummaryNode(), pos)
    or
    pos.isFunctionSelfReference() and n = call.asOrdinaryCall().getCalleeNode()
    or
    pos.isFunctionSelfReference() and n = call.asImpliedLambdaCall().flow()
    or
    exists(Function fun |
      call.asImpliedLambdaCall() = fun and
      CallGraph::impliedReceiverStep(n, TThisNode(fun)) and
      sameContainerAsEnclosingContainer(n, fun) and
      pos.isThis()
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
    or
    result.asLibraryCallable() = node.(FlowSummaryNode).getSummarizedCallable()
    or
    result.asLibraryCallable() =
      node.(FlowSummaryIntermediateAwaitStoreNode).getSummarizedCallable()
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
    or
    node instanceof FlowSummaryIntermediateAwaitStoreNode
    or
    node instanceof CaptureNode
    or
    // Hide function expressions, as capture-flow causes them to appear in unhelpful ways
    // TODO: Instead hide PathNodes with a capture content as the head of its access path?
    node.asExpr() instanceof Function
    or
    node instanceof GenericSynthesizedNode
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

  private import semmle.javascript.frameworks.data.internal.AccessPathSyntax as AccessPathSyntax

  class PropertyName extends string {
    PropertyName() {
      this = any(PropAccess access).getPropertyName()
      or
      this = any(PropertyPattern p).getName()
      or
      this = any(GlobalVariable v).getName()
      or
      this = [0 .. 9].toString()
      or
      this =
        [
          DataFlow::PseudoProperties::arrayElement(), DataFlow::PseudoProperties::mapValueAll(),
          Promises::valueProp(), Promises::errorProp()
        ]
      or
      exists(AccessPathSyntax::AccessPathToken tok |
        tok.getName() = "Member" and this = tok.getAnArgument()
      )
    }
  }

  private predicate isKnownMapKey(string key) {
    exists(MethodCallExpr call |
      call.getMethodName() = "get" and
      call.getNumArgument() = 1 and
      call.getArgument(0).getStringValue() = key
    )
    or
    exists(AccessPathSyntax::AccessPathToken token |
      token.getName() = "MapValue" and
      token.getAnArgument() = key
    )
  }

  newtype TContent =
    MkPropertyNameContent(PropertyName name) or
    MkArrayElementUnknown() or
    MkMapValueWithUnknownKey() or
    MkMapValueWithKnownKey(string key) { isKnownMapKey(key) } or
    MkMapKey() or
    MkSetElement() or
    MkIteratorElement() or
    MkIteratorError() or
    MkCapturedContent(LocalVariable v) { v.isCaptured() }

  class Content extends TContent {
    /**
     * Gets a string representation of this content.
     *
     * Note that these strings are visible to the end-user,
     * as they occur in the access path of path nodes.
     */
    string toString() {
      result = this.asPropertyName()
      or
      result = this.asCapturedVariable().getName()
      or
      this.isUnknownArrayElement() and
      result = "ArrayElement"
      or
      this = MkMapValueWithUnknownKey() and
      result = "MapValue"
      or
      exists(string key |
        this = MkMapValueWithKnownKey(key) and
        result = "MapValue[" + key + "]"
      )
      or
      this = MkMapKey() and
      result = "MapKey"
      or
      this = MkSetElement() and
      result = "SetElement"
      or
      this = MkIteratorElement() and
      result = "IteratorElement"
      or
      this = MkIteratorError() and
      result = "IteratorError"
    }

    string asPropertyName() { this = MkPropertyNameContent(result) }

    pragma[nomagic]
    int asArrayIndex() { result = this.asPropertyName().toInt() and result >= 0 }

    LocalVariable asCapturedVariable() { this = MkCapturedContent(result) }

    predicate isUnknownArrayElement() { this = MkArrayElementUnknown() }

    predicate isMapValueWithUnknownKey() { this = MkMapValueWithUnknownKey() }

    predicate isMapValueWithKnownKey(string key) { this = MkMapValueWithKnownKey(key) }
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
    MkAccessorCall(DataFlow::PropRef node) {
      // Some PropRefs can't result in an accessor call, such as Object.defineProperty.
      // Restrict to PropRefs that can result in an accessor call.
      node = TValueNode(any(PropAccess p)) or
      node = TPropNode(any(PropertyPattern p))
    } or
    MkImpliedLambdaCall(Function f) {
      captures(f, _) or CallGraph::impliedReceiverStep(_, TThisNode(f))
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

    DataFlow::PropRef asAccessorCall() { this = MkAccessorCall(result) }

    DataFlow::PartialInvokeNode asPartialCall() { this = MkPartialCall(result) }

    DataFlow::InvokeNode asBoundCall(int boundArgs) { this = MkBoundCall(result, boundArgs) }

    Function asImpliedLambdaCall() { this = MkImpliedLambdaCall(result) }

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

  private class ImpliedLambdaCall extends DataFlowCall, MkImpliedLambdaCall {
    private Function function;

    ImpliedLambdaCall() { this = MkImpliedLambdaCall(function) }

    override string toString() { result = "[implied lambda call] " + function }

    override predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      function.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    override DataFlowCallable getEnclosingCallable() {
      result.asSourceCallable() = function.getEnclosingContainer()
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

  newtype TParameterPosition =
    MkPositionalParameter(int n) { n = [0 .. getMaxArity()] } or
    MkPositionalLowerBound(int n) { n = [0 .. getMaxArity()] } or
    MkThisParameter() or
    MkFunctionSelfReferenceParameter() or
    MkArgumentsArrayParameter()

  class ParameterPosition extends TParameterPosition {
    predicate isPositionalExact() { this instanceof MkPositionalParameter }

    predicate isPositionalLowerBound() { this instanceof MkPositionalLowerBound }

    predicate isPositionalLike() { this.isPositionalExact() or this.isPositionalLowerBound() }

    int asPositional() { this = MkPositionalParameter(result) }

    int asPositionalLowerBound() { this = MkPositionalLowerBound(result) }

    predicate isThis() { this = MkThisParameter() }

    predicate isFunctionSelfReference() { this = MkFunctionSelfReferenceParameter() }

    predicate isArgumentsArray() { this = MkArgumentsArrayParameter() }

    string toString() {
      result = this.asPositional().toString()
      or
      result = this.asPositionalLowerBound().toString() + ".."
      or
      this.isThis() and result = "this"
      or
      this.isFunctionSelfReference() and result = "function"
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
      node.asPartialCall().getACallbackNode().getAFunctionValue().getFunction()
    or
    exists(DataFlow::InvokeNode invoke, int boundArgs |
      invoke = node.asBoundCall(boundArgs) and
      FlowSteps::callsBound(invoke, result.asSourceCallableNotExterns(), boundArgs)
    )
    or
    result.asSourceCallableNotExterns() = node.asAccessorCall().getAnAccessorCallee().getFunction()
    or
    exists(LibraryCallable callable |
      result = MkLibraryCallable(callable) and
      node.asOrdinaryCall() = [callable.getACall(), callable.getACallSimple()]
    )
    or
    result.asSourceCallableNotExterns() = node.asImpliedLambdaCall()
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
    not node1 instanceof TCapturedVariableNode and
    not node2 instanceof TCapturedVariableNode
    or
    FlowSteps::propertyFlowStep(node1, node2)
    or
    FlowSteps::globalFlowStep(node1, node2)
    or
    node2 = FlowSteps::getThrowTarget(node1)
    or
    FlowSummaryImpl::Private::Steps::summaryLocalStep(node1.(FlowSummaryNode).getSummaryNode(),
      node2.(FlowSummaryNode).getSummaryNode(), true)
    or
    // Step from post-update nodes to local sources of the pre-update node. This emulates how JS usually tracks side effects.
    exists(PostUpdateNode postUpdate |
      node1 = postUpdate and
      node2 = postUpdate.getPreUpdateNode().getALocalSource() and
      node1 != node2 and // exclude trivial edges
      sameContainer(node1, node2)
      // Exclude post-update nodes arising from capture flow. Such edges can cross function boundaries,
      // resulting in jump-steps that interfere with what the capture library is doing.
      // Also, the capture library implements use-use flow, making the backward step unnecessary.
      // not VariableCaptureOutput::capturePostUpdateNode(getClosureNode(postUpdate), _)
    )
  }

  predicate simpleLocalFlowStep(Node node1, Node node2) {
    valuePreservingStep(node1, node2) and
    nodeGetEnclosingCallable(pragma[only_bind_out](node1)) =
      nodeGetEnclosingCallable(pragma[only_bind_out](node2))
    or
    exists(
      FlowSummaryImpl::Private::SummaryNode input, FlowSummaryImpl::Private::SummaryNode output
    |
      FlowSummaryImpl::Private::Steps::summaryStoreStep(input, MkAwaited(), output) and
      node1 = TFlowSummaryNode(input) and
      (
        node2 = TFlowSummaryNode(output) and
        not node2 instanceof PostUpdateNode // When doing a store-back, do not add the local flow edge
        or
        node2 = TFlowSummaryIntermediateAwaitStoreNode(input)
      )
      or
      FlowSummaryImpl::Private::Steps::summaryReadStep(input, MkAwaited(), output) and
      node1 = TFlowSummaryNode(input) and
      node2 = TFlowSummaryNode(output)
    )
    or
    VariableCaptureOutput::localFlowStep(getClosureNode(node1), getClosureNode(node2))
    or
    // NOTE: For consistency with readStep/storeStep, we do not translate these steps to jump steps automatically.
    DataFlow::AdditionalFlowStep::step(node1, node2)
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
    or
    DataFlow::AdditionalFlowStep::jumpStep(node1, node2)
  }

  /**
   * Holds if data can flow from `node1` to `node2` via a read of `c`.  Thus,
   * `node1` references an object with a content `c.getAReadContent()` whose
   * value ends up in `node2`.
   */
  predicate readStep(Node node1, ContentSet c, Node node2) {
    exists(DataFlow::PropRead read |
      node1 = read.getBase() and
      c.asPropertyName() = read.getPropertyName() and
      node2 = read
    )
    or
    exists(ContentSet contentSet |
      FlowSummaryImpl::Private::Steps::summaryReadStep(node1.(FlowSummaryNode).getSummaryNode(),
        contentSet, node2.(FlowSummaryNode).getSummaryNode())
    |
      not isSpecialContentSet(contentSet) and
      c = contentSet
      or
      contentSet = MkAwaited() and
      c = ContentSet::property(Promises::valueProp())
    )
    or
    exists(LocalVariable variable |
      VariableCaptureOutput::readStep(getClosureNode(node1), variable, getClosureNode(node2)) and
      c.asSingleton() = MkCapturedContent(variable)
    )
    or
    DataFlow::AdditionalFlowStep::readStep(node1, c, node2)
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
    or
    FlowSummaryImpl::Private::Steps::summaryStoreStep(node1.(FlowSummaryNode).getSummaryNode(), c,
      node2.(FlowSummaryNode).getSummaryNode()) and
    not isSpecialContentSet(c)
    or
    // Store into Awaited
    exists(
      FlowSummaryImpl::Private::SummaryNode input, FlowSummaryImpl::Private::SummaryNode output
    |
      FlowSummaryImpl::Private::Steps::summaryStoreStep(input, MkAwaited(), output) and
      node1 = TFlowSummaryIntermediateAwaitStoreNode(input) and
      node2 = TFlowSummaryNode(output) and
      c.asPropertyName() = Promises::valueProp()
    )
    or
    exists(LocalVariable variable |
      VariableCaptureOutput::storeStep(getClosureNode(node1), variable, getClosureNode(node2)) and
      c.asSingleton() = MkCapturedContent(variable)
    )
    or
    DataFlow::AdditionalFlowStep::storeStep(node1, c, node2)
  }

  /**
   * Holds if values stored inside content `c` are cleared at node `n`. For example,
   * any value stored inside `f` is cleared at the pre-update node associated with `x`
   * in `x.f = newValue`.
   */
  predicate clearsContent(Node n, ContentSet c) {
    FlowSummaryImpl::Private::Steps::summaryClearsContent(n.(FlowSummaryNode).getSummaryNode(), c)
    or
    // Clear promise content before storing into promise value, to avoid creating nested promises
    n = TFlowSummaryIntermediateAwaitStoreNode(_) and
    c = MkPromiseFilter()
    or
    // After reading from Awaited, the output must not be stored in a promise content
    FlowSummaryImpl::Private::Steps::summaryReadStep(_, MkAwaited(),
      n.(FlowSummaryNode).getSummaryNode()) and
    c = MkPromiseFilter()
    or
    any(AdditionalFlowInternal flow).clearsContent(n, c)
  }

  /**
   * Holds if the value that is being tracked is expected to be stored inside content `c`
   * at node `n`.
   */
  predicate expectsContent(Node n, ContentSet c) {
    FlowSummaryImpl::Private::Steps::summaryExpectsContent(n.(FlowSummaryNode).getSummaryNode(), c)
    or
    // After storing into Awaited, the result must be stored in a promise-content.
    // There is a value step from the input directly to this node, hence the need for expectsContent.
    FlowSummaryImpl::Private::Steps::summaryStoreStep(_, MkAwaited(),
      n.(FlowSummaryNode).getSummaryNode()) and
    c = MkPromiseFilter()
    or
    any(AdditionalFlowInternal flow).expectsContent(n, c)
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
    FlowSummaryImpl::Private::summaryAllowParameterReturnInSelf(p)
    or
    exists(Function f |
      VariableCaptureOutput::heuristicAllowInstanceParameterReturnInSelf(f) and
      p = TFunctionSelfReferenceNode(f)
    )
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
  int getAdditionalFlowIntoCallNodeTerm(ArgumentNode arg, ParameterNode p) { none() }

  pragma[inline]
  predicate golangSpecificParamArgFilter(DataFlowCall call, ParameterNode p, ArgumentNode arg) {
    any()
  }

  class ArgumentNode extends DataFlow::Node {
    ArgumentNode() { isArgumentNodeImpl(this, _, _) }

    predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
      isArgumentNodeImpl(this, call, pos)
    }
  }

  class ParameterNode extends DataFlow::Node {
    ParameterNode() { isParameterNodeImpl(this, _, _) }
  }

  predicate defaultAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    TaintTracking::AdditionalTaintStep::step(node1, node2)
    or
    FlowSummaryImpl::Private::Steps::summaryLocalStep(node1.(FlowSummaryNode).getSummaryNode(),
      node2.(FlowSummaryNode).getSummaryNode(), false)
    or
    // Convert steps into and out of array elements to plain taint steps
    FlowSummaryImpl::Private::Steps::summaryReadStep(node1.(FlowSummaryNode).getSummaryNode(),
      ContentSet::arrayElement(), node2.(FlowSummaryNode).getSummaryNode())
    or
    FlowSummaryImpl::Private::Steps::summaryStoreStep(node1.(FlowSummaryNode).getSummaryNode(),
      ContentSet::arrayElement(), node2.(FlowSummaryNode).getSummaryNode())
    //   and
    // not postUpdatePair(_, node2) // ignore steps into post-update nodes; rely on ordinary content flow for storebacks
    //
    // Note: the JS taint-tracking library has steps that treat store/read as taint steps in many cases,
    // e.g. pushing to an array taints the whole array, and a promise of a tainted value is itself considered tainted.
    // Currently we only do this for arrays, not for promises.
  }

  newtype TContentSet =
    MkSingletonContent(Content content) or
    MkArrayElementKnown(int index) { index = any(PropertyName name).toInt() and index >= 0 } or
    MkArrayElementLowerBound(int index) { index = [0 .. getMaxPreciseArrayIndex() + 1] } or
    MkMapValueKnown(string key) { isKnownMapKey(key) } or
    MkMapValueAll() or
    MkPromiseFilter() or
    MkIteratorFilter() or
    // MkAwaited is used exclusively as an intermediate value in flow summaries.
    // 'Awaited' is encoded as a ContentSummaryComponent, although the flow graph we generate is different
    // than an ordinary content component. This special content set should never appear in a step.
    MkAwaited()

  /**
   * Holds if `cs` is used to encode a special operation as a content component, but should not
   * be treated as an ordinary content component.
   */
  predicate isSpecialContentSet(ContentSet cs) { cs = MkAwaited() }
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
    Private::Content getAStoreContent() {
      result = this.asSingleton()
      or
      // For array element access with known lower bound, just store into the unknown array element
      this = ContentSet::arrayElementLowerBound(_) and
      result.isUnknownArrayElement()
      or
      exists(int n |
        this = ContentSet::arrayElementKnown(n) and
        result.asArrayIndex() = n
      )
      or
      exists(string key |
        this = ContentSet::mapValueWithKnownKey(key) and
        result.isMapValueWithKnownKey(key)
      )
      or
      this = ContentSet::mapValueAll() and
      result.isMapValueWithUnknownKey()
    }

    /** Gets a content that may be read from when reading from this set. */
    pragma[nomagic]
    Private::Content getAReadContent() {
      result = this.asSingleton()
      or
      this.isPromiseFilter() and
      result.asPropertyName() = [Promises::valueProp(), Promises::errorProp()]
      or
      this.isIteratorFilter() and
      (
        result = Private::MkIteratorElement()
        or
        result = Private::MkIteratorError()
      )
      or
      exists(int bound | this = ContentSet::arrayElementLowerBound(bound) |
        result.isUnknownArrayElement()
        or
        result.asArrayIndex() >= bound
      )
      or
      exists(int n | this = ContentSet::arrayElementKnown(n) |
        result.isUnknownArrayElement()
        or
        result.asArrayIndex() = n
      )
      or
      exists(string key | this = ContentSet::mapValueWithKnownKey(key) |
        result.isMapValueWithUnknownKey()
        or
        result.isMapValueWithKnownKey(key)
      )
      or
      this = ContentSet::mapValueAll() and
      (
        result.isMapValueWithUnknownKey()
        or
        result.isMapValueWithKnownKey(_)
      )
    }

    Private::Content asSingleton() { this = Private::MkSingletonContent(result) }

    PropertyName asPropertyName() { result = this.asSingleton().asPropertyName() }

    int asArrayIndex() { result = this.asSingleton().asArrayIndex() }

    predicate isPromiseFilter() { this = ContentSet::promiseFilter() }

    predicate isIteratorFilter() { this = ContentSet::iteratorFilter() }

    predicate isArrayElement() { this = ContentSet::arrayElement() }

    /**
     * Gets a string representation of this content set.
     */
    string toString() {
      result = this.asSingleton().toString()
      or
      this.isPromiseFilter() and result = "PromiseFilter"
      or
      exists(int bound |
        this = ContentSet::arrayElementLowerBound(bound) and
        result = "ArrayElement[" + bound + "..]"
      )
      or
      exists(int n | this = ContentSet::arrayElementKnown(n) and result = "ArrayElement[" + n + "]")
      or
      this = Private::MkAwaited() and result = "Awaited (with coercion)"
      or
      this = ContentSet::mapValueAll() and
      result = "MapValue"
    }
  }

  module ContentSet {
    pragma[inline]
    ContentSet singleton(Private::Content content) { result.asSingleton() = content }

    pragma[inline]
    ContentSet property(Private::PropertyName name) { result.asSingleton().asPropertyName() = name }

    /**
     * A content set that should only be used in `withContent` and `withoutContent` steps, which
     * matches the two promise-related contents, `Awaited[value]` and `Awaited[error]`.
     */
    ContentSet promiseFilter() { result = Private::MkPromiseFilter() }

    /**
     * A content set that should only be used in `withContent` and `withoutContent` steps, which
     * matches the two iterator-related contents, `IteratorElement` and `IteratorError`.
     */
    ContentSet iteratorFilter() { result = Private::MkIteratorFilter() }

    /**
     * A content set describing the result of a resolved promise.
     */
    ContentSet promiseValue() { result = property(Promises::valueProp()) }

    /**
     * A content set describing the error stored in a rejected promise.
     */
    ContentSet promiseError() { result = property(Promises::errorProp()) }

    /**
     * A content set describing all array elements, regardless of their index in the array.
     */
    ContentSet arrayElement() { result = Private::MkArrayElementLowerBound(0) }

    /**
     * A content set describing array elements at index `bound` or greater.
     *
     * For `bound=0` this gets the same content set as `ContentSet::arrayElement()`, that is,
     * the content set describing all array elements.
     *
     * For large values of `bound` this has no result - see `ContentSet::arrayElementLowerBoundFromInt`.
     */
    ContentSet arrayElementLowerBound(int bound) {
      result = Private::MkArrayElementLowerBound(bound)
    }

    /**
     * A content set describing an access to array index `n`.
     *
     * This content set reads from element `n` and the unknown element, and stores to index `n`.
     *
     * For large values of `n` this has no result - see `ContentSet::arrayElementFromInt`.
     */
    ContentSet arrayElementKnown(int n) { result = Private::MkArrayElementKnown(n) }

    /**
     * The singleton content set describing array elements stored at an unknown index.
     */
    ContentSet arrayElementUnknown() { result = singleton(Private::MkArrayElementUnknown()) }

    /**
     * Gets a content set describing array elements at index `bound` or greater.
     *
     * If `bound` is too large, it is truncated to the greatest lower bound we can represent.
     */
    bindingset[bound]
    ContentSet arrayElementLowerBoundFromInt(int bound) {
      result = arrayElementLowerBound(bound.minimum(Private::getMaxPreciseArrayIndex() + 1))
    }

    /**
     * Gets the content set describing an access to array index `n`.
     *
     * If `n` is too large, it is truncated to the greatest lower bound we can represent.
     */
    bindingset[n]
    ContentSet arrayElementFromInt(int n) {
      result = arrayElementKnown(n)
      or
      not exists(arrayElementKnown(n)) and
      result = arrayElementLowerBoundFromInt(n)
    }

    /** Gets the content set describing the keys of a `Map` object. */
    ContentSet mapKey() { result = singleton(Private::MkMapKey()) }

    /** Gets the content set describing the values of a `Map` object stored with an unknown key. */
    ContentSet mapValueWithUnknownKey() { result = singleton(Private::MkMapValueWithUnknownKey()) }

    /**
     * Gets the content set describing the value of a `Map` object stored with the given known `key`.
     *
     * This has no result if `key` is not one of the keys we track precisely. See also `mapValueFromKey`.
     */
    ContentSet mapValueWithKnownKeyStrict(string key) { result = Private::MkMapValueKnown(key) }

    /**
     * Gets the content set describing an access to a map value with the given `key`.
     *
     * This content set also reads from a value stored with an unknown key. Use `mapValueWithKnownKeyStrict` to strictly
     * refer to known keys.
     *
     * This has no result if `key` is not one of the keys we track precisely. See also `mapValueFromKey`.
     */
    ContentSet mapValueWithKnownKey(string key) {
      result = singleton(Private::MkMapValueWithKnownKey(key))
    }

    /** Gets the content set describing all values in a map (with known or unknown key). */
    ContentSet mapValueAll() { result = Private::MkMapValueAll() }

    /**
     * Gets the content set describing the value in a `Map` object stored at the given `key`.
     *
     * If `key` is not one of the keys we track precisely, this is mapped to the unknown key instead.
     */
    bindingset[key]
    ContentSet mapValueFromKey(string key) {
      result = mapValueWithKnownKey(key)
      or
      not exists(mapValueWithKnownKey(key)) and
      result = mapValueWithUnknownKey()
    }

    /** Gets the content set describing the elements of a `Set` object. */
    ContentSet setElement() { result = singleton(Private::MkSetElement()) }

    /** Gets the content set describing the elements of an iterator object. */
    ContentSet iteratorElement() { result = singleton(Private::MkIteratorElement()) }

    /** Gets the content set describing the exception to be thrown when attempting to iterate over the given value. */
    ContentSet iteratorError() { result = singleton(Private::MkIteratorError()) }
  }
}
