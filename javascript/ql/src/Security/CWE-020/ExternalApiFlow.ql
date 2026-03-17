/**
 * @kind path-problem
 */

import semmle.javascript.internal.unified.minimal.minimal
import semmle.javascript.internal.unified.JSUnified

module FlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {
    exists(Call call |
      not exists(CallGraph::viableCallableFromSource(call)) and
      node.isValueOf(call.getUnderlyingInvokeExpr())
    )
  }

  predicate isSink(DataFlow::Node node) {
    exists(Call call |
      not exists(CallGraph::viableCallableFromSource(call)) and
      node.isValueOf(call.getUnderlyingInvokeExpr().getAnArgument())
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }
}

module Flow = DataFlow::Global<FlowConfig>;

import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink)
select sink.getNode(), source, sink, "Flow here"
