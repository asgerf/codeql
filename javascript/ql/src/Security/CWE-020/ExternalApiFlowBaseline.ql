/**
 * @name External API flow
 * @id js/external-api-flow-baseline
 * @kind path-problem
 */

import javascript

module FlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {
    exists(DataFlow::InvokeNode call |
      not exists(call.getACallee()) and
      node = call
    )
  }

  predicate isSink(DataFlow::Node node) {
    exists(DataFlow::InvokeNode call |
      not exists(call.getACallee()) and
      node = call.getAnArgument()
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }
}

module Flow = DataFlow::Global<FlowConfig>;

import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink)
select sink.getNode(), source, sink, "Flow here"
