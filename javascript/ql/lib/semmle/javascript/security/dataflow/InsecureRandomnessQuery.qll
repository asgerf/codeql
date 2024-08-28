/**
 * Provides a taint tracking configuration for reasoning about random
 * values that are not cryptographically secure.
 *
 * Note, for performance reasons: only import this file if
 * `InsecureRandomness::Configuration` is needed, otherwise
 * `InsecureRandomnessCustomizations` should be imported instead.
 */

import javascript
private import semmle.javascript.security.SensitiveActions
import InsecureRandomnessCustomizations::InsecureRandomness
private import InsecureRandomnessCustomizations::InsecureRandomness as InsecureRandomness

/**
 * A taint tracking configuration for random values that are not cryptographically secure.
 */
module InsecureRandomnessConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) { node instanceof Sanitizer }

  predicate isBarrierOut(DataFlow::Node node) {
    // stop propagation at the sinks to avoid double reporting
    isSink(node)
  }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    InsecureRandomness::isAdditionalTaintStep(pred, succ)
    or
    // We want to make use of default taint steps but not the default taint sanitizers, as they
    // generally assume numbers aren't taintable. So we use a data-flow configuration that includes all
    // taint steps as additional flow steps.
    TaintTracking::defaultTaintStep(pred, succ)
  }
}

/**
 * Taint tracking for random values that are not cryptographically secure.
 */
module InsecureRandomnessFlow = DataFlow::Global<InsecureRandomnessConfig>;

/**
 * DEPRECATED. Use the `InsecureRandomnessFlow` module instead.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "InsecureRandomness" }

  override predicate isSource(DataFlow::Node source) { source instanceof Source }

  override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  override predicate isSanitizer(DataFlow::Node node) {
    // not making use of `super.isSanitizer`: those sanitizers are not for this kind of data
    node instanceof Sanitizer
  }

  override predicate isSanitizerOut(DataFlow::Node node) {
    // stop propagation at the sinks to avoid double reporting
    this.isSink(node)
  }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    InsecureRandomness::isAdditionalTaintStep(pred, succ)
  }
}
