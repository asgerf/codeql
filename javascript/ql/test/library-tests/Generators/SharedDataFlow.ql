import javascript
import testUtilities.ConsistencyChecking

module ConfigArg implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source.asExpr().getStringValue() = "source" }

  predicate isSink(DataFlow::Node sink) {
    sink = any(DataFlow::CallNode call | call.getCalleeName() = "sink").getAnArgument()
  }
}

module Configuration = DataFlow::Global<ConfigArg>;

class ConsistencyConfig extends ConsistencyConfiguration {
  ConsistencyConfig() { this = "ConsistencyConfig" }

  override DataFlow::Node getAnAlert() { Configuration::flow(_, result) }
}
