/**
 * Provides a taint tracking configuration for reasoning about
 * tainted-path vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `TaintedPath::Configuration` is needed, otherwise
 * `TaintedPathCustomizations` should be imported instead.
 */

import javascript
private import TaintedPathCustomizations::TaintedPath
private import semmle.javascript.dataflow2.DataFlow as DataFlow2

// Materialize flow labels
private class ConcretePosixPath extends Label::PosixPath {
  ConcretePosixPath() { this = this }
}

private class ConcreteSplitPath extends Label::SplitPath {
  ConcreteSplitPath() { this = this }
}

/**
 * A taint-tracking configuration for reasoning about tainted-path vulnerabilities.
 */
module ConfigurationArgs implements DataFlow::StateConfigSig {
  predicate isSource(DataFlow::Node source, DataFlow::FlowLabel state) {
    state = source.(Source).getAFlowLabel()
  }

  predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel state) {
    state = sink.(Sink).getAFlowLabel()
  }

  predicate isBarrier(DataFlow::Node node, DataFlow::FlowLabel label) {
    node instanceof Sanitizer and exists(label)
  }

  predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) { guard instanceof BarrierGuardNode }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, DataFlow::FlowLabel state1, DataFlow::Node node2,
    DataFlow::FlowLabel state2
  ) {
    isAdditionalTaintedPathFlowStep(node1, node2, state1, state2)
  }
}

module Configuration = DataFlow::GlobalWithState<ConfigurationArgs>;
