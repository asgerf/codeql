/**
 * Provides a taint-tracking configuration for reasoning about reflected
 * cross-site scripting vulnerabilities.
 */

import javascript
import ReflectedXssCustomizations::ReflectedXss
private import Xss::Shared as SharedXss

module ConfigurationArgs implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) { node instanceof Sanitizer }

  private predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) {
    guard instanceof QuoteGuard or
    guard instanceof ContainsHtmlGuard
  }
}

module Configuration = TaintTracking::Global<ConfigurationArgs>;

/**
 * A taint-tracking configuration for reasoning about XSS.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "ReflectedXss" }

  override predicate isSource(DataFlow::Node source) { source instanceof Source }

  override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof Sanitizer
  }

  override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode guard) {
    guard instanceof QuoteGuard or
    guard instanceof ContainsHtmlGuard
  }
}

private class QuoteGuard extends TaintTracking::SanitizerGuardNode, SharedXss::QuoteGuard {
  QuoteGuard() { this = this }
}

private class ContainsHtmlGuard extends TaintTracking::SanitizerGuardNode,
  SharedXss::ContainsHtmlGuard
{
  ContainsHtmlGuard() { this = this }
}
