/**
 * @kind path-problem
 */

import semmle.javascript.internal.unified.minimal.minimal
import semmle.javascript.internal.unified.JSUnified

module FlowConfig implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow2::Node node) {
    exists(Call call |
      not exists(CallGraph::viableCallableFromSource(call)) and
      node.isValueOf(call.getUnderlyingInvokeExpr())
    )
  }

  predicate isSink(DataFlow2::Node node) {
    exists(Call call |
      not exists(CallGraph::viableCallableFromSource(call)) and
      node.isValueOf(call.getUnderlyingInvokeExpr().getAnArgument())
    )
  }

  predicate isAdditionalFlowStep(DataFlow2::Node node1, DataFlow2::Node node2) { none() }

  predicate isBarrier(DataFlow2::Node node) { none() }
}

module Flow = DataFlow2::Global<FlowConfig>;

import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink)
select sink.getNode(), source, sink, "Flow here"
