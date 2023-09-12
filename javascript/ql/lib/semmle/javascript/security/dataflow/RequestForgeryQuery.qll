/**
 * Provides a taint-tracking configuration for reasoning about request
 * forgery.
 *
 * Note, for performance reasons: only import this file if
 * `RequestForgery::Configuration` is needed, otherwise
 * `RequestForgeryCustomizations` should be imported instead.
 */

import javascript
import UrlConcatenation
import RequestForgeryCustomizations::RequestForgery

module ConfigurationArgs implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source.(Source).isServerSide() }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) { node instanceof Sanitizer }

  predicate isBarrierOut(DataFlow::Node node) { sanitizingPrefixEdge(node, _) }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    isAdditionalRequestForgeryStep(pred, succ)
  }
}

module Configuration = TaintTracking::Global<ConfigurationArgs>;

/**
 * A taint tracking configuration for request forgery.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "RequestForgery" }

  override predicate isSource(DataFlow::Node source) { ConfigurationArgs::isSource(source) }

  override predicate isSink(DataFlow::Node sink) { ConfigurationArgs::isSink(sink) }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node)
    or
    node instanceof Sanitizer
  }

  override predicate isSanitizerOut(DataFlow::Node node) { ConfigurationArgs::isBarrierOut(node) }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    ConfigurationArgs::isAdditionalFlowStep(pred, succ)
  }
}
