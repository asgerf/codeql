/**
 * INTERNAL: Do not use outside the data flow library.
 *
 * Contains the raw data type underlying `DataFlow::Node`.
 */

private import javascript
private import semmle.javascript.dataflow2.FlowSummaryImpl as FlowSummaryImpl

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
  TDestructuredModuleImportNode(ImportDeclaration decl) {
    exists(decl.getASpecifier().getImportedName())
  } or
  THtmlAttributeNode(HTML::Attribute attr) or
  TFunctionReturnNode(Function f) or
  TExceptionalFunctionReturnNode(Function f) or
  TExceptionalInvocationReturnNode(InvokeExpr e) or
  TGlobalAccessPathRoot() or
  TTemplatePlaceholderTag(Templating::TemplatePlaceholderTag tag) or
  TReflectiveParametersNode(Function f) or
  /** A synthesized node to decompose load-store steps into two steps through an intermediate expectsContent node. */
  TSynthExpectPromiseNode(InvokeExpr e, string prop) {
    prop = [Promises::valueProp(), Promises::errorProp()]
  }

/**
 * A data-flow node that is not a flow summary node.
 *
 * Imports are needed for pruning irrelevant flow summaries, and imports can therefore not depend on
 * TFlowSummaryNode.
 *
 * This node should thus only be used for the purpose of computing imports without creating a dependency on
 * TFlowSummaryNode.
 */
class TEarlyStageNode =
  TValueNode or TSsaDefNode or TCapturedVariableNode or TPropNode or TRestPatternNode or
      TElementPatternNode or TElementNode or TReflectiveCallNode or TThisNode or
      TDestructuredModuleImportNode or THtmlAttributeNode or TFunctionReturnNode or
      TExceptionalFunctionReturnNode or TExceptionalInvocationReturnNode or TGlobalAccessPathRoot or
      TTemplatePlaceholderTag or TReflectiveParametersNode or TSynthExpectPromiseNode;
