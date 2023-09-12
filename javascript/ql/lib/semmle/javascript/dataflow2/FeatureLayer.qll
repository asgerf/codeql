private import javascript
private import semmle.javascript.dataflow2.BarrierGuards
private import semmle.javascript.dataflow2.DeduplicateFlowState
private import semmle.javascript.dataflow2.DataFlow as SharedDataFlow

class FlowState = DataFlow::FlowLabel;

/**
 * The public parts of the shared-data flow API, with some features shadowed by JS-specific wrappers.
 */
module Public {
  import SharedDataFlow // Re-export while shadowing original signatures

  class Node = DataFlow::Node; // Needed to resolve an ambiguity between two other aliases

  //
  // The following is a copy of ConfigSig and StateConfigSig with two changes:
  //  - The addition of `isBarrierGuard`
  //  - `FlowState` is not part of the signature, and is instead fixed to `DataFlow::FlowLabel`.
  //
  /** An input configuration for data flow. */
  signature module ConfigSig {
    default predicate isBarrierGuard(DataFlow::BarrierGuardNode node) { none() }

    /**
     * Holds if `source` is a relevant data flow source.
     */
    predicate isSource(Node source);

    /**
     * Holds if `sink` is a relevant data flow sink.
     */
    predicate isSink(Node sink);

    /**
     * Holds if data flow through `node` is prohibited. This completely removes
     * `node` from the data flow graph.
     */
    default predicate isBarrier(Node node) { none() }

    /** Holds if data flow into `node` is prohibited. */
    default predicate isBarrierIn(Node node) { none() }

    /** Holds if data flow out of `node` is prohibited. */
    default predicate isBarrierOut(Node node) { none() }

    /**
     * Holds if data may flow from `node1` to `node2` in addition to the normal data-flow steps.
     */
    default predicate isAdditionalFlowStep(Node node1, Node node2) { none() }

    /**
     * Holds if an arbitrary number of implicit read steps of content `c` may be
     * taken at `node`.
     */
    default predicate allowImplicitRead(Node node, ContentSet c) { none() }

    /**
     * Holds if `node` should never be skipped over in the `PathGraph` and in path
     * explanations.
     */
    default predicate neverSkip(Node node) {
      isAdditionalFlowStep(node, _) or isAdditionalFlowStep(_, node)
    }

    /**
     * Gets the virtual dispatch branching limit when calculating field flow.
     * This can be overridden to a smaller value to improve performance (a
     * value of 0 disables field flow), or a larger value to get more results.
     */
    default int fieldFlowBranchLimit() { result = 2 }

    /**
     * Gets a data flow configuration feature to add restrictions to the set of
     * valid flow paths.
     *
     * - `FeatureHasSourceCallContext`:
     *    Assume that sources have some existing call context to disallow
     *    conflicting return-flow directly following the source.
     * - `FeatureHasSinkCallContext`:
     *    Assume that sinks have some existing call context to disallow
     *    conflicting argument-to-parameter flow directly preceding the sink.
     * - `FeatureEqualSourceSinkCallContext`:
     *    Implies both of the above and additionally ensures that the entire flow
     *    path preserves the call context.
     *
     * These features are generally not relevant for typical end-to-end data flow
     * queries, but should only be used for constructing paths that need to
     * somehow be pluggable in another path context.
     */
    default FlowFeature getAFeature() { none() }

    /** Holds if sources should be grouped in the result of `flowPath`. */
    default predicate sourceGrouping(Node source, string sourceGroup) { none() }

    /** Holds if sinks should be grouped in the result of `flowPath`. */
    default predicate sinkGrouping(Node sink, string sinkGroup) { none() }

    /**
     * Holds if hidden nodes should be included in the data flow graph.
     *
     * This feature should only be used for debugging or when the data flow graph
     * is not visualized (as it is in a `path-problem` query).
     */
    default predicate includeHiddenNodes() { none() }
  }

  /** An input configuration for data flow using flow state. */
  signature module StateConfigSig {
    default predicate isBarrierGuard(DataFlow::BarrierGuardNode node) { none() }

    /**
     * Holds if `source` is a relevant data flow source with the given initial
     * `state`.
     */
    predicate isSource(Node source, FlowState state);

    /**
     * Holds if `sink` is a relevant data flow sink accepting `state`.
     */
    predicate isSink(Node sink, FlowState state);

    /**
     * Holds if `sink` is a relevant data flow sink for any state.
     */
    default predicate isSink(Node sink) { none() }

    /**
     * Holds if data flow through `node` is prohibited. This completely removes
     * `node` from the data flow graph.
     */
    default predicate isBarrier(Node node) { none() }

    /**
     * Holds if data flow through `node` is prohibited when the flow state is
     * `state`.
     */
    default predicate isBarrier(Node node, FlowState state) { none() }

    /** Holds if data flow into `node` is prohibited. */
    default predicate isBarrierIn(Node node) { none() }

    /** Holds if data flow out of `node` is prohibited. */
    default predicate isBarrierOut(Node node) { none() }

    /**
     * Holds if data may flow from `node1` to `node2` in addition to the normal data-flow steps.
     */
    default predicate isAdditionalFlowStep(Node node1, Node node2) { none() }

    /**
     * Holds if data may flow from `node1` to `node2` in addition to the normal data-flow steps.
     * This step is only applicable in `state1` and updates the flow state to `state2`.
     */
    default predicate isAdditionalFlowStep(
      Node node1, FlowState state1, Node node2, FlowState state2
    ) {
      none()
    }

    /**
     * Holds if an arbitrary number of implicit read steps of content `c` may be
     * taken at `node`.
     */
    default predicate allowImplicitRead(Node node, ContentSet c) { none() }

    /**
     * Holds if `node` should never be skipped over in the `PathGraph` and in path
     * explanations.
     */
    default predicate neverSkip(Node node) {
      isAdditionalFlowStep(node, _) or
      isAdditionalFlowStep(_, node) or
      isAdditionalFlowStep(node, _, _, _) or
      isAdditionalFlowStep(_, _, node, _)
    }

    /**
     * Gets the virtual dispatch branching limit when calculating field flow.
     * This can be overridden to a smaller value to improve performance (a
     * value of 0 disables field flow), or a larger value to get more results.
     */
    default int fieldFlowBranchLimit() { result = 2 }

    /**
     * Gets a data flow configuration feature to add restrictions to the set of
     * valid flow paths.
     *
     * - `FeatureHasSourceCallContext`:
     *    Assume that sources have some existing call context to disallow
     *    conflicting return-flow directly following the source.
     * - `FeatureHasSinkCallContext`:
     *    Assume that sinks have some existing call context to disallow
     *    conflicting argument-to-parameter flow directly preceding the sink.
     * - `FeatureEqualSourceSinkCallContext`:
     *    Implies both of the above and additionally ensures that the entire flow
     *    path preserves the call context.
     *
     * These features are generally not relevant for typical end-to-end data flow
     * queries, but should only be used for constructing paths that need to
     * somehow be pluggable in another path context.
     */
    default FlowFeature getAFeature() { none() }

    /** Holds if sources should be grouped in the result of `flowPath`. */
    default predicate sourceGrouping(Node source, string sourceGroup) { none() }

    /** Holds if sinks should be grouped in the result of `flowPath`. */
    default predicate sinkGrouping(Node sink, string sinkGroup) { none() }

    /**
     * Holds if hidden nodes should be included in the data flow graph.
     *
     * This feature should only be used for debugging or when the data flow graph
     * is not visualized (as it is in a `path-problem` query).
     */
    default predicate includeHiddenNodes() { none() }
  }

  /**
   * An empty set of barrier guards.
   *
   * We don't want to use `AdditionalBarrierGuardNode` here, as it forces evaluation of parts of the
   * old data flow library. There are no nodes in it other than derived ones, which we get anyway.
   */
  abstract private class EmptyGuard extends DataFlow::BarrierGuardNode { }

  /** Constructs a global data flow computation. */
  module Global<ConfigSig S> implements SharedDataFlow::GlobalFlowSig {
    import SharedDataFlow::Global<Convert<S, EmptyGuard>>
  }

  /** Constructs a global data flow computation using flow state. */
  module GlobalWithState<StateConfigSig S> implements SharedDataFlow::GlobalFlowSig {
    import SharedDataFlow::GlobalWithState<ConvertWithState<S, EmptyGuard>>
  }
}

import Conversions

private module Conversions {
  private import javascript::DataFlow

  //
  // TODO: Pass in the `DefaultSanitizerGuards::barrierGuardBlocksNode` predicate instead, to avoid repeating this work for each query.
  //
  /** Either `AdditionalBarrierGuardNode` or `AdditionalSanitizerGuardNode`. */
  signature class AdditionalGuardClass extends DataFlow::BarrierGuardNode;

  module Convert<ConfigSig C, AdditionalGuardClass AdditionalGuard> implements
    SharedDataFlow::ConfigSig
  {
    private predicate isBarrierGuard(DataFlow::BarrierGuardNode node) {
      C::isBarrierGuard(node)
      or
      node instanceof AdditionalGuard
    }

    private import MakeBarrierGuards<isBarrierGuard/1>

    predicate isSource(Node source) { C::isSource(source) }

    predicate isSink(Node sink) { C::isSink(sink) }

    predicate isBarrier(Node node) {
      C::isBarrier(node) or barrierGuardBlocksNode(node) or barrierGuardBlocksNode(node, _)
    }

    predicate isBarrierIn(Node node) { C::isBarrierIn(node) }

    predicate isBarrierOut(Node node) { C::isBarrierOut(node) }

    predicate isAdditionalFlowStep(Node node1, Node node2) { C::isAdditionalFlowStep(node1, node2) }

    predicate allowImplicitRead(Node node, ContentSet c) { C::allowImplicitRead(node, c) }

    predicate neverSkip(Node node) { C::neverSkip(node) }

    int fieldFlowBranchLimit() { result = C::fieldFlowBranchLimit() }

    FlowFeature getAFeature() { result = C::getAFeature() }

    predicate sourceGrouping(Node source, string sourceGroup) {
      C::sourceGrouping(source, sourceGroup)
    }

    predicate sinkGrouping(Node sink, string sinkGroup) { C::sinkGrouping(sink, sinkGroup) }

    predicate includeHiddenNodes() { C::includeHiddenNodes() }
  }

  module ConvertWithState<StateConfigSig C, AdditionalGuardClass AdditionalGuard> implements
    SharedDataFlow::StateConfigSig
  {
    class FlowState = DataFlow::FlowLabel;

    private predicate isBarrierGuard(DataFlow::BarrierGuardNode node) {
      C::isBarrierGuard(node)
      or
      node instanceof AdditionalGuard
    }

    // import MakeDeduplicateFlowState<C::isSource/2, C::isSink/2>
    private import MakeBarrierGuards<isBarrierGuard/1>

    predicate isSource = C::isSource/2;

    predicate isSink = C::isSink/2;

    predicate isSink(Node sink) { none() } // FIXME: forward C::isSink to MakeDeduplicateFlowState

    predicate isBarrier(Node node) { C::isBarrier(node) or barrierGuardBlocksNode(node) }

    predicate isBarrier(Node node, FlowState state) {
      C::isBarrier(node, state)
      or
      // deduplicationBarrier(node, state) or
      barrierGuardBlocksNode(node, state)
    }

    predicate isBarrierIn(Node node) { C::isBarrierIn(node) }

    predicate isBarrierOut(Node node) { C::isBarrierOut(node) }

    predicate isAdditionalFlowStep(Node node1, Node node2) { C::isAdditionalFlowStep(node1, node2) }

    predicate isAdditionalFlowStep(Node node1, FlowState state1, Node node2, FlowState state2) {
      C::isAdditionalFlowStep(node1, state1, node2, state2) //or
      // deduplicationStep(node1, state1, node2, state2)
    }

    predicate allowImplicitRead(Node node, ContentSet c) { C::allowImplicitRead(node, c) }

    predicate neverSkip(Node node) { C::neverSkip(node) }

    int fieldFlowBranchLimit() { result = C::fieldFlowBranchLimit() }

    FlowFeature getAFeature() { result = C::getAFeature() }

    predicate sourceGrouping(Node source, string sourceGroup) {
      C::sourceGrouping(source, sourceGroup)
    }

    predicate sinkGrouping(Node sink, string sinkGroup) { C::sinkGrouping(sink, sinkGroup) }

    predicate includeHiddenNodes() { C::includeHiddenNodes() }

    predicate hideFinalFlowStates() {
      any() // yes please
    }
  }
}
