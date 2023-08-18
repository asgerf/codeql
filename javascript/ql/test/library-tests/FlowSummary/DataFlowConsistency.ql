import javascript
import semmle.javascript.dataflow2.DataFlowImplSpecific::Private
import semmle.javascript.dataflow2.DataFlowImplConsistency::Consistency

class Config extends ConsistencyConfiguration {
  override predicate missingLocationExclude(DataFlow::Node n) {
    n instanceof FlowSummaryNode
    or
    n instanceof FlowSummaryIntermediateAwaitStoreNode
    or
    n = DataFlow::globalAccessPathRootPseudoNode()
  }

  override predicate uniqueNodeLocationExclude(DataFlow::Node n) { this.missingLocationExclude(n) }
}
