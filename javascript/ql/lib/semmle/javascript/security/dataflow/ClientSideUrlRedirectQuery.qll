/**
 * Provides a taint-tracking configuration for reasoning about
 * unvalidated URL redirection problems on the client side.
 *
 * Note, for performance reasons: only import this file if
 * `ClientSideUrlRedirect::Configuration` is needed, otherwise
 * `ClientSideUrlRedirectCustomizations` should be imported instead.
 */

import javascript
import UrlConcatenation
import ClientSideUrlRedirectCustomizations::ClientSideUrlRedirect
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards

// Materialize flow labels
private class ConcreteDocumentUrl extends DocumentUrl {
  ConcreteDocumentUrl() { this = this }
}

module ConfigurationArg implements DataFlow2::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  predicate isSource(DataFlow::Node source, FlowState state) {
    source.(Source).getAFlowLabel() = state
  }

  predicate isSink(DataFlow::Node sink, FlowState state) {
    sink instanceof Sink and state.isTaint()
  }

  predicate isBarrier(DataFlow::Node node, FlowState state) {
    node instanceof Sanitizer
    or
    barrierGuardBlocksNode(_, node, state)
  }

  predicate isBarrierOut(DataFlow::Node node) { hostnameSanitizingPrefixEdge(node, _) }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, FlowState state1, DataFlow::Node node2, FlowState state2
  ) {
    untrustedUrlSubstring(node1, node2) and
    state1 instanceof DocumentUrl and
    state2.isTaint()
    or
    // preserve document.url label in step from `location` to `location.href` or `location.toString()`
    state1 instanceof DocumentUrl and
    state2 instanceof DocumentUrl and
    (
      node2.(DataFlow::PropRead).accesses(node1, "href")
      or
      exists(DataFlow::CallNode call |
        call.getCalleeName() = "toString" and
        node1 = call.getReceiver() and
        node2 = call
      )
    )
    or
    exists(HtmlSanitizerCall call |
      node1 = call.getInput() and
      node2 = call and
      state1 = state2
    )
  }
}

module Configuration = TaintTracking2::GlobalWithState<ConfigurationArg>;

/**
 * A taint-tracking configuration for reasoning about unvalidated URL redirections.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "ClientSideUrlRedirect" }

  override predicate isSource(DataFlow::Node source, DataFlow::FlowLabel lbl) {
    source.(Source).getAFlowLabel() = lbl
  }

  override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof Sanitizer
  }

  override predicate isSanitizerOut(DataFlow::Node node) { hostnameSanitizingPrefixEdge(node, _) }

  override predicate isAdditionalFlowStep(
    DataFlow::Node node1, DataFlow::Node node2, DataFlow::FlowLabel state1,
    DataFlow::FlowLabel state2
  ) {
    ConfigurationArg::isAdditionalFlowStep(node1, state1, node2, state2)
  }

  override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode guard) {
    guard instanceof HostnameSanitizerGuard
  }
}
