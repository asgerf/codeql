/**
 * @name Information disclosure through postMessage
 * @description Tracks values from an 'authKey' property into a postMessage call with unrestricted origin,
 *              indicating a leak of sensitive information.
 * @kind path-problem
 * @problem.severity warning
 * @tags security
 * @id js/examples/information-disclosure
 */

import javascript
import DataFlow

/**
 * A dataflow configuration that tracks authentication tokens ("authKey")
 * to a postMessage call with unrestricted target origin.
 *
 * For example:
 * ```
 * win.postMessage(JSON.stringify({
 *  action: 'pause',
 *  auth: {
 *    key: window.state.authKey
 *  }
 * }), '*');
 * ```
 */
module AuthKeyTrackingConfig implements DataFlow::ConfigSig {
  predicate isSource(Node node) { node.(PropRead).getPropertyName() = "authKey" }

  predicate isSink(Node node) {
    exists(MethodCallNode call |
      call.getMethodName() = "postMessage" and
      call.getArgument(1).getStringValue() = "*" and // no restriction on target origin
      call.getArgument(0) = node
    )
  }

  predicate isAdditionalFlowStep(Node pred, Node succ) {
    // Step into objects: x -> { f: x }
    succ.(SourceNode).getAPropertyWrite().getRhs() = pred
    or
    // Step through JSON serialization: x -> JSON.stringify(x)
    // Note: TaintTracking::Configuration includes this step by default, but not DataFlow::Configuration
    exists(CallNode call |
      call = globalVarRef("JSON").getAMethodCall("stringify") and
      pred = call.getArgument(0) and
      succ = call
    )
  }
}

module AuthKeyTracking = DataFlow::Global<AuthKeyTrackingConfig>;

import AuthKeyTracking::PathGraph

from PathNode source, PathNode sink
where AuthKeyTracking::flowPath(source, sink)
select sink.getNode(), source, sink, "Message leaks the authKey from $@.", source.getNode(), "here"
