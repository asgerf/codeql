/**
 * Provides a taint-tracking configuration for reasoning about
 * unvalidated URL redirection problems on the server side.
 *
 * Note, for performance reasons: only import this file if
 * `ServerSideUrlRedirect::Configuration` is needed, otherwise
 * `ServerSideUrlRedirectCustomizations` should be imported instead.
 */

import javascript
import RemoteFlowSources
import UrlConcatenation
import ServerSideUrlRedirectCustomizations::ServerSideUrlRedirect
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards

module ConfigurationArg implements DataFlow2::ConfigSig {
  import DefaultSanitizerGuards

  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) {
    node instanceof Sanitizer
    or
    barrierGuardBlocksNode(node)
  }

  predicate isBarrierOut(DataFlow::Node node) { hostnameSanitizingPrefixEdge(node, _) }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(HtmlSanitizerCall call |
      pred = call.getInput() and
      succ = call
    )
  }
}

module Configuration = TaintTracking2::Global<ConfigurationArg>;

/**
 * A taint-tracking configuration for reasoning about unvalidated URL redirections.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "ServerSideUrlRedirect" }

  override predicate isSource(DataFlow::Node source) { source instanceof Source }

  override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof Sanitizer
  }

  override predicate isSanitizerOut(DataFlow::Node node) { ConfigurationArg::isBarrierOut(node) }

  override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode guard) {
    guard instanceof LocalUrlSanitizingGuard or
    guard instanceof HostnameSanitizerGuard
  }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    ConfigurationArg::isAdditionalFlowStep(pred, succ)
  }
}

/**
 * A call to a function called `isLocalUrl` or similar, which is
 * considered to sanitize a variable for purposes of URL redirection.
 */
class LocalUrlSanitizingGuard extends TaintTracking::SanitizerGuardNode, DataFlow::CallNode {
  LocalUrlSanitizingGuard() { this.getCalleeName().regexpMatch("(?i)(is_?)?local_?url") }

  override predicate sanitizes(boolean outcome, Expr e) {
    // `isLocalUrl(e)` sanitizes `e` if it evaluates to `true`
    this.getAnArgument().asExpr() = e and
    outcome = true
  }
}
