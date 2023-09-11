/**
 * Provides a taint tracking configuration for reasoning about
 * tainted-path vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `TaintedPath::Configuration` is needed, otherwise
 * `TaintedPathCustomizations` should be imported instead.
 */

import javascript
private import TaintedPathCustomizations::TaintedPath as TaintedPath
import TaintedPath
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.BarrierGuards
private import semmle.javascript.dataflow2.DeduplicateFlowState

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
module ConfigurationArgs implements DataFlow2::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  private predicate isSourceRaw(DataFlow::Node source, FlowState state) {
    state = source.(Source).getAFlowLabel()
  }

  private predicate isSinkRaw(DataFlow::Node sink, FlowState state) {
    state = sink.(Sink).getAFlowLabel()
  }

  import MakeDeduplicateFlowState<isSourceRaw/2, isSinkRaw/2>

  private predicate isBarrierGuard(DataFlow::BarrierGuardNode node) {
    node instanceof TaintedPath::BarrierGuardNode
  }

  private import MakeBarrierGuards<isBarrierGuard/1>

  predicate isBarrier(DataFlow::Node node, DataFlow::FlowLabel label) {
    node instanceof Sanitizer and exists(label)
    or
    barrierGuardBlocksNode(node, label)
    or
    deduplicationBarrier(node, label)
  }

  predicate isBarrier(DataFlow::Node node) { barrierGuardBlocksNode(node) }

  // predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) { guard instanceof BarrierGuardNode }
  predicate isAdditionalFlowStep(
    DataFlow::Node node1, DataFlow::FlowLabel state1, DataFlow::Node node2,
    DataFlow::FlowLabel state2
  ) {
    isAdditionalTaintedPathFlowStep(node1, node2, state1, state2)
    or
    deduplicationStep(node1, state1, node2, state2)
  }
}

module Configuration = DataFlow2::GlobalWithState<ConfigurationArgs>;
