import javascript
import testUtilities.ConsistencyChecking
import Summaries

DataFlow::CallNode getACall(string name) {
  result.getCalleeName() = name
  or
  result.getCalleeNode().getALocalSource() = DataFlow::globalVarRef(name)
}

module ConfigArg implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { node = getACall("source") }

  predicate isSink(DataFlow::Node node) { node = getACall("sink").getAnArgument() }

  predicate isBarrierGuard(DataFlow::BarrierGuardNode node) { node instanceof BasicBarrierGuard }

  predicate isBarrier(DataFlow::Node node) {
    node.(DataFlow::InvokeNode).getCalleeName().matches("sanitizer_%")
  }
}

module Configuration = DataFlow::Global<ConfigArg>;

class BasicBarrierGuard extends DataFlow::BarrierGuardNode, DataFlow::CallNode {
  BasicBarrierGuard() { this = getACall("isSafe") }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and e = this.getArgument(0).asExpr()
  }
}

class ConsistencyConfig extends ConsistencyConfiguration {
  ConsistencyConfig() { this = "ConsistencyConfig" }

  override DataFlow::Node getAnAlert() { Configuration::flow(_, result) }
}
