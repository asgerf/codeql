import javascript

module TestConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source.asExpr().getStringValue() = "source" }

  predicate isSink(DataFlow::Node sink) {
    sink = any(DataFlow::CallNode call | call.getCalleeName() = "sink").getAnArgument()
  }
}

module TestFlow = TaintTracking::Global<TestConfig>;

class LegacyConfig extends TaintTracking::Configuration {
  LegacyConfig() { this = "LegacyConfig" }

  override predicate isSource(DataFlow::Node source) { TestConfig::isSource(source) }

  override predicate isSink(DataFlow::Node sink) { TestConfig::isSink(sink) }
}

import testUtilities.LegacyDataFlowDiff::DataFlowDiff<TestFlow, LegacyConfig>

query predicate flow = TestFlow::flow/2;
