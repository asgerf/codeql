import javascript
import testUtilities.ConsistencyChecking
import semmle.javascript.security.dataflow.DomBasedXssQuery

class ConsistencyConfig extends ConsistencyConfiguration {
  ConsistencyConfig() { this = "ConsistencyConfig" }

  override DataFlow::Node getAnAlert() { Configuration::flow(_, result) }
}
