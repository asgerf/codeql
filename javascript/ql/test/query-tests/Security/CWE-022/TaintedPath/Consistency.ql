import javascript
import semmle.javascript.security.dataflow.TaintedPathQuery
import testUtilities.ConsistencyChecking

class TestConfig extends ConsistencyConfiguration {
  TestConfig() { this = "TestConfig" }

  override DataFlow::Node getAnAlert() { Configuration::flowTo(result) }
}
