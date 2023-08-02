/**
 * Provides a taint tracking configuration for reasoning about
 * command-injection vulnerabilities (CWE-078).
 *
 * Note, for performance reasons: only import this file if
 * `CommandInjection::Configuration` is needed, otherwise
 * `CommandInjectionCustomizations` should be imported instead.
 */

import javascript
import CommandInjectionCustomizations::CommandInjection
import IndirectCommandArgument
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards

/**
 * Holds if `sink` is a data flow sink for command-injection vulnerabilities, and
 * the alert should be placed at the node `highlight`.
 */
predicate isSinkWithHighlight(DataFlow::Node sink, DataFlow::Node highlight) {
  sink instanceof Sink and highlight = sink
  or
  isIndirectCommandArgument(sink, highlight)
}

module ConfigurationArgs implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { isSinkWithHighlight(sink, _) }

  predicate isBarrier(DataFlow::Node node) { node instanceof Sanitizer }
}

module Configuration = TaintTracking2::Global<ConfigurationArgs>;

/**
 * A taint-tracking configuration for reasoning about command-injection vulnerabilities.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "CommandInjection" }

  override predicate isSource(DataFlow::Node source) { ConfigurationArgs::isSource(source) }

  override predicate isSink(DataFlow::Node sink) { ConfigurationArgs::isSink(sink) }

  override predicate isSanitizer(DataFlow::Node node) { ConfigurationArgs::isBarrier(node) }
}
