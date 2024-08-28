import javascript
import semmle.javascript.dataflow.InferredTypes
import testUtilities.ConsistencyChecking

DataFlow::CallNode getACall(string name) {
  result.getCalleeName() = name
  or
  result.getCalleeNode().getALocalSource() = DataFlow::globalVarRef(name)
}

module TestConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { node = getACall("source") }

  predicate isSink(DataFlow::Node node) { node = getACall("sink").getAnArgument() }

  predicate isBarrier(DataFlow::Node node) {
    node.(DataFlow::InvokeNode).getCalleeName().matches("sanitizer_%") or
    node = DataFlow::MakeBarrierGuard<BasicSanitizerGuard>::getABarrierNode() or
    node = TaintTracking::AdHocWhitelistCheckSanitizer::getABarrierNode()
  }
}

module TestFlow = TaintTracking::Global<TestConfig>;

class LegacyConfig extends TaintTracking::Configuration {
  LegacyConfig() { this = "LegacyConfig" }

  override predicate isSource(DataFlow::Node node) { TestConfig::isSource(node) }

  override predicate isSink(DataFlow::Node node) { TestConfig::isSink(node) }

  override predicate isSanitizer(DataFlow::Node node) {
    node.(DataFlow::InvokeNode).getCalleeName().matches("sanitizer_%")
  }

  override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode node) {
    node instanceof BasicSanitizerGuard or
    node instanceof TaintTracking::AdHocWhitelistCheckSanitizer
  }
}

import testUtilities.LegacyDataFlowDiff::DataFlowDiff<TestFlow, LegacyConfig>

class BasicSanitizerGuard extends TaintTracking::SanitizerGuardNode, DataFlow::CallNode {
  BasicSanitizerGuard() { this = getACall("isSafe") }

  override predicate sanitizes(boolean outcome, Expr e) { this.blocksExpr(outcome, e) }

  predicate blocksExpr(boolean outcome, Expr e) {
    outcome = true and e = this.getArgument(0).asExpr()
  }
}

query predicate flow = TestFlow::flow/2;

class Consistency extends ConsistencyConfiguration {
  Consistency() { this = "Consistency" }

  override DataFlow::Node getAnAlert() { TestFlow::flowTo(result) }
}
