/**
 * @kind path-problem
 */

import semmle.javascript.internal.unified.JSUnified
import semmle.javascript.internal.unified.minimal.minimal

module TestConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { node = ModelsAsDataFinal::getASource("test-source") }

  predicate isSink(DataFlow::Node node) { node = ModelsAsDataFinal::getASink("test-sink") }
}

module TestFlow = TaintTracking::Global<TestConfig>;

import TestFlow::PathGraph

from TestFlow::PathNode source, TestFlow::PathNode sink
where TestFlow::flowPath(source, sink)
select sink.getNode(), source, sink, "Flow here"
