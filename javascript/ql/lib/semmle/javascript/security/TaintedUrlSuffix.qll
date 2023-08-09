/**
 * Provides a flow label for reasoning about URLs with a tainted query and fragment part,
 * which we collectively refer to as the "suffix" of the URL.
 */

import javascript

/**
 * Provides a flow label for reasoning about URLs with a tainted query and fragment part,
 * which we collectively refer to as the "suffix" of the URL.
 */
module TaintedUrlSuffix {
  private import DataFlow

  /**
   * The flow label representing a URL with a tainted query and fragment part.
   *
   * Can also be accessed using `TaintedUrlSuffix::label()`.
   */
  class TaintedUrlSuffixLabel extends FlowLabel {
    TaintedUrlSuffixLabel() { this = "tainted-url-suffix" }
  }

  /**
   * Gets the flow label representing a URL with a tainted query and fragment part.
   */
  FlowLabel label() { result instanceof TaintedUrlSuffixLabel }

  /** Gets a remote flow source that is a tainted URL query or fragment part from `window.location`. */
  ClientSideRemoteFlowSource source() {
    result = DOM::locationRef().getAPropertyRead(["search", "hash"])
    or
    result = DOM::locationSource()
    or
    result.getKind().isUrl()
  }

  /** Holds if `read` accesses a property is not tainted by the query/fragment part of the URL. */
  private predicate isSafeLocationProp(DataFlow::PropRead read) {
    // Ignore properties that refer to the scheme, domain, port, auth, or path.
    read.getPropertyName() =
      [
        "protocol", "scheme", "host", "hostname", "domain", "origin", "port", "path", "pathname",
        "username", "password", "auth"
      ]
  }

  /**
   * Holds if `node` should be a barrier for flow into the given `label` (which is always bound to the tainted-url-suffix label).
   */
  predicate isBarrier(DataFlow::Node node, DataFlow::FlowLabel label) {
    isSafeLocationProp(node) and label = label()
  }

  /**
   * DEPRECATED. Should only be used with the legacy `DataFlow::Configuration` class.
   *
   * Holds if the taint step `src -> dst` should preserve the tainted-url-suffix label.
   *
   * This predicate is unnecessary with the new data flow library, because flow states in a taint-tracking configuration
   * include all taint steps by default.
   */
  pragma[inline]
  deprecated predicate preservingTaintStep(Node src, Node dst, FlowLabel srclbl, FlowLabel dstlbl) {
    // Inherit all ordinary taint steps except `x -> x.p` steps
    srclbl = label() and
    dstlbl = label() and
    TaintTracking::sharedTaintStep(src, dst) and
    not isSafeLocationProp(dst)
  }

  /**
   * Holds if there is a flow step `src -> dst` involving the URL suffix taint label.
   *
   * This handles steps through string operations, promises, URL parsers, and URL accessors.
   */
  predicate step(Node src, Node dst, FlowLabel srclbl, FlowLabel dstlbl) {
    // Transition from URL suffix to full taint when extracting the query/fragment part.
    srclbl = label() and
    dstlbl.isTaint() and
    (
      exists(MethodCallNode call, string name |
        src = call.getReceiver() and
        dst = call and
        name = call.getMethodName()
      |
        // Substring that is not a prefix
        name = StringOps::substringMethodName() and
        not call.getArgument(0).getIntValue() = 0
        or
        // Split around '#' or '?' and extract the suffix
        name = "split" and
        call.getArgument(0).getStringValue() = ["#", "?"] and
        not exists(call.getAPropertyRead("0")) // Avoid false flow to the prefix
        or
        // Replace '#' and '?' with nothing
        name = "replace" and
        call.getArgument(0).getStringValue() = ["#", "?"] and
        call.getArgument(1).getStringValue() = ""
        or
        // The `get` call in `url.searchParams.get(x)` and `url.hashParams.get(x)`
        // The step should be safe since nothing else reachable by this flow label supports a method named 'get'.
        name = "get"
        or
        // Methods on URL objects from the Closure library
        name = "getDecodedQuery"
        or
        name = "getFragment"
        or
        name = "getParameterValue"
        or
        name = "getParameterValues"
        or
        name = "getQueryData"
      )
      or
      exists(PropRead read |
        src = read.getBase() and
        dst = read and
        // Unlike the `search` property, the `query` property from `url.parse` does not include the `?`.
        read.getPropertyName() = "query"
      )
      or
      // Assume calls to regexp.exec always extract query/fragment parameters.
      exists(MethodCallNode call |
        call = any(RegExpLiteral re).flow().(DataFlow::SourceNode).getAMethodCall("exec") and
        src = call.getArgument(0) and
        dst = call
      )
    )
  }
}
