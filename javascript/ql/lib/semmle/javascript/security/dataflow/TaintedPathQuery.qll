/**
 * Provides a taint tracking configuration for reasoning about
 * tainted-path vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `TaintedPath::Configuration` is needed, otherwise
 * `TaintedPathCustomizations` should be imported instead.
 */

import javascript
import TaintedPathCustomizations::TaintedPath
private import semmle.javascript.dataflow2.DataFlow as SharedLib
private import semmle.javascript.dataflow2.BarrierGuards

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
module ConfigurationArgs implements SharedLib::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  predicate isSource(DataFlow::Node source, DataFlow::FlowLabel label) {
    label = source.(Source).getAFlowLabel()
  }

  predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel label) {
    label = sink.(Sink).getAFlowLabel()
  }

  predicate isBarrier(DataFlow::Node node, DataFlow::FlowLabel label) {
    node instanceof Sanitizer and exists(label)
    or
    barrierGuardBlocksNode(_, node, label)
    or
    barrierGuardBlocksNode(_, node, "") and exists(label)
  }

  // predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) { guard instanceof BarrierGuardNode }
  predicate isAdditionalFlowStep(
    DataFlow::Node src, DataFlow::FlowLabel srclabel, DataFlow::Node dst,
    DataFlow::FlowLabel dstlabel
  ) {
    isAdditionalTaintedPathFlowStep(src, dst, srclabel, dstlabel)
  }
}

module Configuration = SharedLib::GlobalWithState<ConfigurationArgs>;
