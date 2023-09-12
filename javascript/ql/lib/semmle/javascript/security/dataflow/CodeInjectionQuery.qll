/**
 * Provides a taint-tracking configuration for reasoning about code
 * injection vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `CodeInjection::Configuration` is needed, otherwise
 * `CodeInjectionCustomizations` should be imported instead.
 */

import javascript
import CodeInjectionCustomizations::CodeInjection

module ConfigurationArgs implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) { node instanceof Sanitizer }

  predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    // HTML sanitizers are insufficient protection against code injection
    node1 = node2.(HtmlSanitizerCall).getInput()
  }
}

module Configuration = TaintTracking::Global<ConfigurationArgs>;

/**
 * A taint-tracking configuration for reasoning about code injection vulnerabilities.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "CodeInjection" }

  override predicate isSource(DataFlow::Node source) { source instanceof Source }

  override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof Sanitizer
  }

  override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    ConfigurationArgs::isAdditionalFlowStep(node1, node2)
  }
}
