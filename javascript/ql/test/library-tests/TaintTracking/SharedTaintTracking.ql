import javascript
import semmle.javascript.dataflow.InferredTypes
import testUtilities.ConsistencyChecking

DataFlow::CallNode getACall(string name) {
  result.getCalleeName() = name
  or
  result.getCalleeNode().getALocalSource() = DataFlow::globalVarRef(name)
}

module ConfigArg implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { node = getACall("source") }

  predicate isSink(DataFlow::Node node) { node = getACall("sink").getAnArgument() }

  predicate isBarrier(DataFlow::Node node) {
    node.(DataFlow::InvokeNode).getCalleeName().matches("sanitizer_%")
  }

  predicate isBarrierGuard(DataFlow::BarrierGuardNode node) {
    node instanceof TaintTracking::AdHocWhitelistCheckSanitizer or
    node instanceof BasicBarrierGuard
  }
}

module Configuration = TaintTracking::Global<ConfigArg>;

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
