/**
 * Provides a taint-tracking configuration for reasoning about DOM-based
 * cross-site scripting vulnerabilities.
 */

import javascript
private import semmle.javascript.security.TaintedUrlSuffix
import DomBasedXssCustomizations::DomBasedXss
private import Xss::Shared as Shared
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards
private import semmle.javascript.dataflow2.DeduplicateFlowState

/**
 * A sink that is not a URL write or a JQuery selector,
 * assumed to be a value that is interpreted as HTML.
 */
class HtmlSink extends DataFlow::Node instanceof Sink {
  HtmlSink() {
    not this instanceof WriteUrlSink and
    not this instanceof JQueryHtmlOrSelectorSink
  }
}

/** DEPRECATED: Alias for HtmlSink */
deprecated class HTMLSink = HtmlSink;

module ConfigurationArgs implements DataFlow2::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  private predicate isSourceRaw(DataFlow::Node source, DataFlow::FlowLabel label) {
    source instanceof Source and
    (label.isTaint() or label = prefixLabel()) and
    not source = TaintedUrlSuffix::source()
    or
    source = TaintedUrlSuffix::source() and
    label = TaintedUrlSuffix::label()
  }

  private predicate isSinkRaw(DataFlow::Node sink, DataFlow::FlowLabel label) {
    sink instanceof HtmlSink and
    label = [TaintedUrlSuffix::label(), prefixLabel(), DataFlow::FlowLabel::taint()]
    or
    sink instanceof JQueryHtmlOrSelectorSink and
    label = [DataFlow::FlowLabel::taint(), prefixLabel()]
    or
    sink instanceof WriteUrlSink and
    label = prefixLabel()
  }

  import MakeDeduplicateFlowState<isSourceRaw/2, isSinkRaw/2>

  private predicate isBarrierGuard(DataFlow::BarrierGuardNode node) {
    node instanceof PrefixStringSanitizer or
    node instanceof ContainsHtmlGuard
  }

  import MakeSanitizerGuards<isBarrierGuard/1>

  predicate isBarrier(DataFlow::Node node) {
    node instanceof Sanitizer
    or
    barrierGuardBlocksNode(node)
  }

  predicate isBarrier(DataFlow::Node node, DataFlow::FlowLabel lbl) {
    barrierGuardBlocksNode(node, lbl)
    or
    // copy all taint barrier guards to the TaintedUrlSuffix/PrefixLabel label
    barrierGuardBlocksNode(node, DataFlow::FlowLabel::taint()) and
    lbl = [TaintedUrlSuffix::label(), prefixLabel()]
    or
    // any non-first string-concatenation leaf is a barrier for the prefix label.
    exists(StringOps::ConcatenationRoot root |
      node = root.getALeaf() and
      not node = root.getFirstLeaf() and
      lbl = prefixLabel()
    )
    or
    // we assume that `.join()` calls have a prefix, and thus block the prefix label.
    node = any(DataFlow::MethodCallNode call | call.getMethodName() = "join") and
    lbl = prefixLabel()
    or
    isOptionallySanitizedNode(node) and
    lbl = [DataFlow::FlowLabel::taint(), prefixLabel(), TaintedUrlSuffix::label()]
    or
    TaintedUrlSuffix::isBarrier(node, lbl)
    or
    deduplicationBarrier(node, lbl)
  }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, FlowState state1, DataFlow::Node node2, FlowState state2
  ) {
    TaintedUrlSuffix::step(node1, node2, state1, state2)
    or
    exists(DataFlow::Node operator |
      StringConcatenation::taintStep(node1, node2, operator, _) and
      StringConcatenation::getOperand(operator, 0).getStringValue() = "<" + any(string s) and
      state1 = TaintedUrlSuffix::label() and
      state2.isTaint()
    )
    or
    // steps out of taintedSuffixlabel to taint-label are also steps to prefixLabel.
    TaintedUrlSuffix::step(node1, node2, TaintedUrlSuffix::label(), DataFlow::FlowLabel::taint()) and
    state1 = TaintedUrlSuffix::label() and
    state2 = prefixLabel()
    or
    exists(DataFlow::FunctionNode callback, DataFlow::Node arg |
      any(JQuery::MethodCall c).interpretsArgumentAsHtml(arg) and
      callback = arg.getABoundFunctionValue(_) and
      node1 = callback.getReturnNode() and
      node2 = callback and
      state1 = state2
    )
    or
    deduplicationStep(node1, state1, node2, state2)
  }
}

module Configuration = TaintTracking2::GlobalWithState<ConfigurationArgs>;

/**
 * A taint-tracking configuration for reasoning about XSS.
 * Both ordinary HTML sinks, URL sinks, and JQuery selector based sinks.
 * - HTML sinks are sinks for any tainted value
 * - URL sinks are only sinks when the scheme is user controlled
 * - JQuery selector sinks are sinks when the tainted value can start with `<`.
 *
 * The above is achieved using three flow labels:
 * - TaintedUrlSuffix: a URL where the attacker only controls a suffix.
 * - Taint: a tainted value where the attacker controls part of the value.
 * - PrefixLabel: a tainted value where the attacker controls the prefix
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "HtmlInjection" }

  override predicate isSource(DataFlow::Node source, DataFlow::FlowLabel label) {
    ConfigurationArgs::isSource(source, label)
  }

  override predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel label) {
    ConfigurationArgs::isSink(sink, label)
  }

  override predicate isSanitizer(DataFlow::Node node) { ConfigurationArgs::isBarrier(node) }

  override predicate isLabeledBarrier(DataFlow::Node node, DataFlow::FlowLabel lbl) {
    ConfigurationArgs::isBarrier(node, lbl)
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node node1, DataFlow::Node node2, DataFlow::FlowLabel state1,
    DataFlow::FlowLabel state2
  ) {
    ConfigurationArgs::isAdditionalFlowStep(node1, state1, node2, state2)
    or
    // inherit all ordinary taint steps for the prefix label
    state1 = prefixLabel() and
    state2 = prefixLabel() and
    TaintTracking::sharedTaintStep(node1, node2)
    or
    // inherit some ordinary taint steps for tainted-url-suffix label
    TaintedUrlSuffix::preservingTaintStep(node1, node2, state1, state2)
  }
}

private class PrefixStringSanitizerActivated extends TaintTracking::SanitizerGuardNode,
  PrefixStringSanitizer
{
  PrefixStringSanitizerActivated() { this = this }
}

private class PrefixStringActivated extends DataFlow::FlowLabel, PrefixString {
  PrefixStringActivated() { this = this }
}

private class QuoteGuard extends TaintTracking::SanitizerGuardNode, Shared::QuoteGuard {
  QuoteGuard() { this = this }
}

private class ContainsHtmlGuard extends TaintTracking::SanitizerGuardNode, Shared::ContainsHtmlGuard
{
  ContainsHtmlGuard() { this = this }
}
