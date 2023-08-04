/**
 * Provides a taint-tracking configuration for reasoning about reflected
 * cross-site scripting vulnerabilities.
 */

import javascript
import ReflectedXssCustomizations::ReflectedXss
private import Xss::Shared as SharedXss
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards

module ConfigurationArgs implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) {
    node instanceof Sanitizer
    or
    barrierGuardBlocksNode(node, _)
  }
}

module Configuration = TaintTracking2::Global<ConfigurationArgs>;

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
