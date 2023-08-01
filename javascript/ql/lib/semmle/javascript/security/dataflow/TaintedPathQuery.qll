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
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.BarrierGuards

// Materialize flow labels
private class ConcretePosixPath extends Label::PosixPath {
  ConcretePosixPath() { this = this }
}

private class ConcreteSplitPath extends Label::SplitPath {
  ConcreteSplitPath() { this = this }
}

private class SourceState extends DataFlow::FlowLabel {
  SourceState() { this = "SourceState" }
}

private class SinkState extends DataFlow::FlowLabel {
  SinkState() { this = "SinkState" }
}

/**
 * A taint-tracking configuration for reasoning about tainted-path vulnerabilities.
 */
module ConfigurationArgs implements DataFlow2::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  predicate isSource(DataFlow::Node source, DataFlow::FlowLabel label) {
    source instanceof Source and label instanceof SourceState
  }

  predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel label) {
    sink instanceof Sink and label instanceof SinkState
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
    or
    exists(Source source |
      src = source and
      dst = source and
      srclabel instanceof SourceState and
      dstlabel = source.getAFlowLabel()
    )
    or
    exists(Sink sink |
      src = sink and
      dst = sink and
      srclabel = sink.getAFlowLabel() and
      dstlabel instanceof SinkState
    )
  }
}

module Configuration = DataFlow2::GlobalWithState<ConfigurationArgs>;
