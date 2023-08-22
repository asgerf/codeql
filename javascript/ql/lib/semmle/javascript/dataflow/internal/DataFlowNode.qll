/**
 * INTERNAL: Do not use outside the data flow library.
 *
 * Contains the raw data type underlying `DataFlow::Node`.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlowImplSpecific::Private as DataFlowPrivate
private import semmle.javascript.dataflow2.FlowSummaryImpl as FlowSummaryImpl
private import semmle.javascript.dataflow2.FlowSummaryImplSpecific as FlowSummaryImplSpecific

/**
 * The raw data type underlying `DataFlow::Node`.
 */
cached
newtype TNode =
  TValueNode(AST::ValueNode nd) or
  TSsaDefNode(SsaDefinition d) or
  TCapturedVariableNode(LocalVariable v) { v.isCaptured() } or
  TPropNode(@property p) or
  TRestPatternNode(DestructuringPattern dp, Expr rest) { rest = dp.getRest() } or
  TElementPatternNode(ArrayPattern ap, Expr p) { p = ap.getElement(_) } or
  TElementNode(ArrayExpr arr, Expr e) { e = arr.getAnElement() } or
  TReflectiveCallNode(MethodCallExpr ce, string kind) {
    ce.getMethodName() = kind and
    (kind = "call" or kind = "apply")
  } or
  TThisNode(StmtContainer f) { f.(Function).getThisBinder() = f or f instanceof TopLevel } or
  TFunctionSelfReferenceNode(Function f) or
  TDestructuredModuleImportNode(ImportDeclaration decl) {
    exists(decl.getASpecifier().getImportedName())
  } or
  THtmlAttributeNode(HTML::Attribute attr) or
  TFunctionReturnNode(Function f) or
  TAsyncFunctionIntermediateStoreReturnNode(Function f) { f.isAsync() } or
  TExceptionalFunctionReturnNode(Function f) or
  TExceptionalInvocationReturnNode(InvokeExpr e) or
  TGlobalAccessPathRoot() or
  TTemplatePlaceholderTag(Templating::TemplatePlaceholderTag tag) or
  TReflectiveParametersNode(Function f) or
  TExprPostUpdateNode(Expr e) {
    e = any(InvokeExpr invoke).getAnArgument() or
    e = any(PropAccess access).getBase() or
    e = any(InvokeExpr invoke).getCallee()
  } or
  TConstructorThisArgumentNode(InvokeExpr e) { e instanceof NewExpr or e instanceof SuperCall } or
  TFlowSummaryNode(FlowSummaryImpl::Private::SummaryNode sn) or
  TFlowSummaryIntermediateAwaitStoreNode(FlowSummaryImpl::Private::SummaryNode sn) {
    FlowSummaryImpl::Private::Steps::summaryStoreStep(sn, DataFlowPrivate::MkAwaited(), _)
  }

/**
 * A data-flow node that is not a flow summary node.
 *
 * This node exists to avoid an unwanted dependency on flow summaries in some parts of the codebase
 * that should not depend on them.
 *
 * In particular, this dependency chain must not result in negative recursion:
 * - Flow summaries can only be created after pruning irrelevant flow summaries
 * - To prune irrelevant flow summaries, we must know which packages are imported
 * - To know which packages are imported, module systems must be evaluated
 * - The AMD and NodeJS module systems rely on data flow to find calls to `require` and similar.
 *   These module systems must therefore use `TEarlyStageNode` instead of `DataFlow::Node`.
 */
class TEarlyStageNode =
  TValueNode or TSsaDefNode or TCapturedVariableNode or TPropNode or TRestPatternNode or
      TElementPatternNode or TElementNode or TReflectiveCallNode or TThisNode or
      TFunctionSelfReferenceNode or TDestructuredModuleImportNode or THtmlAttributeNode or
      TFunctionReturnNode or TExceptionalFunctionReturnNode or TExceptionalInvocationReturnNode or
      TGlobalAccessPathRoot or TTemplatePlaceholderTag or TReflectiveParametersNode or
      TExprPostUpdateNode or TConstructorThisArgumentNode;
