private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.StepSummary
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import FlowSummaryImpl as FlowSummaryImpl
private import semmle.javascript.internal.flow_summaries.Promises2
private import semmle.javascript.internal.flow_summaries.Strings2
private import VariableCaptureSpecific

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
      not fun.isAsyncOrGenerator() // exception is not thrown, but will be stored on the returned promise object
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
    exists(Expr expr |
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

  predicate isArgumentNode(Node n, DataFlowCall call, ArgumentPosition pos) {
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

  private newtype TContent =
    MkPropertyNameContent(PropertyName name) or
    MkCapturedContent(LocalVariable v) { v.isCaptured() }

  class Content extends TContent {
    string toString() {
      result = this.asPropertyName()
      or
      result = this.asCapturedVariable().getName()
    }

    string asPropertyName() { this = MkPropertyNameContent(result) }

    LocalVariable asCapturedVariable() { this = MkCapturedContent(result) }
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
    MkAccessorCall(DataFlow::PropRef node) or
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
    MkThisParameter() or
    MkFunctionSelfReferenceParameter() or
    MkArgumentsArrayParameter()

  class ParameterPosition extends TParameterPosition {
    predicate isPositional() { this instanceof MkPositionalParameter }

    int asPositional() { this = MkPositionalParameter(result) }

    predicate isThis() { this = MkThisParameter() }

    predicate isFunctionSelfReference() { this = MkFunctionSelfReferenceParameter() }

    predicate isArgumentsArray() { this = MkArgumentsArrayParameter() }

    string toString() {
      result = this.asPositional().toString()
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
    result.asSourceCallable() = node.asAccessorCall().getAnAccessorCallee().getFunction()
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
    node1.getASuccessor() = node2 and
    not node1 instanceof TCapturedVariableNode and
    not node2 instanceof TCapturedVariableNode
    or
    DataFlow::SharedFlowStep::step(node1, node2)
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
      // Exclude post-update nodes arising from capture flow. Such edges can cross function boundaries,
      // resulting in jump-steps that interfere with what the capture library is doing.
      // Also, the capture library implements use-use flow, making the backward step unnecessary.
      not VariableCaptureOutput::capturePostUpdateNode(getClosureNode(postUpdate), _)
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
    exists(AwaitExpr await |
      // Allow non-promise values to propagate through await. The target node has clearsContent.
      node1 = await.getOperand().flow() and
      node2 = await.flow()
    )
    or
    exists(Function f |
      f.isAsync() and
      node1 = f.getAReturnedExpr().flow()
    |
      node2 = TAsyncFunctionIntermediateStoreReturnNode(f) // clears promise-content
      or
      node2 = TFunctionReturnNode(f) // expects promise-content
    )
    or
    VariableCaptureOutput::localFlowStep(getClosureNode(node1), getClosureNode(node2))
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
      c.asPropertyName() = read.getPropertyName() and
      node2 = read
    )
    or
    DataFlow::SharedFlowStep::loadStep(node1, node2, c.asPropertyName()) and
    // Exclude promise-related steps because we want these to be entirely modelled with flow summaries now
    not isPromiseProperty(c)
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
    exists(AwaitExpr await | node1 = await.getOperand().flow() |
      node2 = await.flow() and
      c.asPropertyName() = Promises::valueProp()
      or
      node2 = await.getExceptionTarget() and
      c.asPropertyName() = Promises::errorProp()
    )
    or
    exists(LocalVariable variable |
      VariableCaptureOutput::readStep(getClosureNode(node1), variable, getClosureNode(node2)) and
      c.asSingleton() = MkCapturedContent(variable)
    )
  }

  pragma[nomagic]
  private predicate isPromiseProperty(ContentSet cs) {
    cs = [ContentSet::promiseValue(), ContentSet::promiseError()]
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
    exists(DataFlow::ArrayCreationNode array, int i |
      node1 = array.getElement(i) and
      node2 = array
    |
      if i = [0 .. 9]
      then c.asPropertyName() = i.toString()
      else c.asPropertyName() = DataFlow::PseudoProperties::arrayElement()
    )
    or
    DataFlow::SharedFlowStep::storeStep(node1, node2, c.asPropertyName()) and
    // Exclude promise-related steps because we want these to be entirely modelled with flow summaries now
    not isPromiseProperty(c)
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
    exists(Function f | f.isAsync() |
      node1 = TAsyncFunctionIntermediateStoreReturnNode(f) and
      node2 = TFunctionReturnNode(f) and
      c.asPropertyName() = Promises::valueProp()
      or
      // Store thrown exceptions in the promise-error
      node1 = TExceptionalFunctionReturnNode(f) and
      node2 = TFunctionReturnNode(f) and
      c.asPropertyName() = Promises::errorProp()
    )
    or
    exists(LocalVariable variable |
      VariableCaptureOutput::storeStep(getClosureNode(node1), variable, getClosureNode(node2)) and
      c.asSingleton() = MkCapturedContent(variable)
    )
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
    // Result of 'await' cannot be a promise; needed for the local flow step into 'await'
    exists(AwaitExpr await |
      n = await.flow() and
      c = MkPromiseFilter()
    )
    or
    n = TAsyncFunctionIntermediateStoreReturnNode(_) and
    c = MkPromiseFilter()
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
    exists(Function f |
      f.isAsync() and
      n = TFunctionReturnNode(f) and
      c = MkPromiseFilter()
    )
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

  newtype TContentSet =
    MkSingletonContent(Content content) or
    MkPromiseFilter() or
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
    Private::Content getAStoreContent() { result = this.asSingleton() }

    /** Gets a content that may be read from when reading from this set. */
    pragma[nomagic]
    Private::Content getAReadContent() {
      result = this.asSingleton()
      or
      this.isPromiseFilter() and
      result.asPropertyName() = [Promises::valueProp(), Promises::errorProp()]
    }

    Private::Content asSingleton() { this = Private::MkSingletonContent(result) }

    PropertyName asPropertyName() { result = this.asSingleton().asPropertyName() }

    predicate isPromiseFilter() { this = ContentSet::promiseFilter() }

    string toString() {
      result = this.asSingleton().toString()
      or
      this.isPromiseFilter() and result = "promiseFilter()"
      or
      this = Private::MkAwaited() and result = "Awaited (with coercion)"
    }
  }

  module ContentSet {
    pragma[inline]
    ContentSet singleton(Private::Content content) { result.asSingleton() = content }

    pragma[inline]
    ContentSet property(Private::PropertyName name) { result.asSingleton().asPropertyName() = name }

    /**
     * A content set that should only be used in `withContent` and `withoutContent` steps, which
     * matches the two promise-related contents, `Awaited` and `AwaitedError`.
     */
    ContentSet promiseFilter() { result = Private::MkPromiseFilter() }

    /**
     * A content set describing the result of a resolved promise.
     */
    ContentSet promiseValue() { result = property(Promises::valueProp()) }

    /**
     * A content set describing the error stored in a rejected promise.
     */
    ContentSet promiseError() { result = property(Promises::errorProp()) }
  }
}

private import semmle.javascript.dataflow2.FlowSummary

class FlowFromSideEffectOnParameter extends SummarizedCallable {
  FlowFromSideEffectOnParameter() { this = "flowFromSideEffectOnParameter" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = this }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Parameter[0].Member[prop]" and
    output = "ReturnValue" and
    preservesValue = true
  }
}
