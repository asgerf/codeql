import javascript
import semmle.javascript.dataflow2.DataFlowImplSpecific::Private
import semmle.javascript.dataflow2.DataFlowImplConsistency::Consistency
import semmle.javascript.dataflow.internal.DataFlowNode

private predicate isAmbientNode(DataFlow::Node node) {
  exists(AstNode n | n.isAmbient() |
    node = TValueNode(n) or
    node = TThisNode(n) or
    node = TReflectiveParametersNode(n) or
    node = TPropNode(n) or
    node = TFunctionSelfReferenceNode(n) or
    node = TAsyncFunctionIntermediateStoreReturnNode(n) or
    node = TExceptionalFunctionReturnNode(n) or
    node = TExprPostUpdateNode(n) or
    node = TExceptionalInvocationReturnNode(n) or
    node = TDestructuredModuleImportNode(n)
  )
}

class Config extends ConsistencyConfiguration {
  override predicate missingLocationExclude(DataFlow::Node n) {
    n instanceof FlowSummaryNode
    or
    n instanceof FlowSummaryIntermediateAwaitStoreNode
    or
    n = DataFlow::globalAccessPathRootPseudoNode()
  }

  override predicate uniqueNodeLocationExclude(DataFlow::Node n) { this.missingLocationExclude(n) }

  override predicate uniqueEnclosingCallableExclude(DataFlow::Node n) { isAmbientNode(n) }

  override predicate uniqueCallEnclosingCallableExclude(DataFlowCall call) {
    isAmbientNode(call.asOrdinaryCall()) or
    isAmbientNode(call.asAccessorCall())
  }
}
