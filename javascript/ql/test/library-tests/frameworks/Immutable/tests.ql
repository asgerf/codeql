import javascript
private import semmle.javascript.dataflow.internal.StepSummary

module TestConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source.(DataFlow::CallNode).getCalleeName() = "source"
  }

  predicate isSink(DataFlow::Node sink) {
    exists(DataFlow::CallNode call | call.getCalleeName() = "sink" | call.getAnArgument() = sink)
  }
}

module TestFlow = DataFlow::Global<TestConfig>;

class LegacyConfig extends DataFlow::Configuration {
  LegacyConfig() { this = "Config" }

  override predicate isSource(DataFlow::Node source) { TestConfig::isSource(source) }

  override predicate isSink(DataFlow::Node sink) { TestConfig::isSink(sink) }
}

query predicate dataFlow = TestFlow::flow/2;

import testUtilities.LegacyDataFlowDiff::DataFlowDiff<TestFlow, LegacyConfig>
