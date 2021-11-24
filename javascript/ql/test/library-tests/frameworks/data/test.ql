import javascript
import testUtilities.ConsistencyChecking

class Steps extends ModelInput::SummaryModelCsv {
  override predicate row(string row) {
    // package;type;path;input;output;kind
    row =
      [
        "testlib;;Member[preserveTaint];Argument[0];ReturnValue;taint",
        "testlib;;Member[taintIntoCallback];Argument[0];Argument[1..2].Parameter[0];taint",
        "testlib;;Member[preserveArgZeroAndTwo];Argument[0,2];ReturnValue;taint",
        "testlib;;Member[preserveAllButFirstArgument];Argument[1..];ReturnValue;taint"
      ]
  }
}

class BasicTaintTracking extends TaintTracking::Configuration {
  BasicTaintTracking() { this = "BasicTaintTracking" }

  override predicate isSource(DataFlow::Node source) {
    source.(DataFlow::CallNode).getCalleeName() = "source"
  }

  override predicate isSink(DataFlow::Node sink) {
    sink = any(DataFlow::CallNode call | call.getCalleeName() = "sink").getAnArgument()
  }
}

query predicate taintFlow(DataFlow::Node source, DataFlow::Node sink) {
  any(BasicTaintTracking tr).hasFlow(source, sink)
}
