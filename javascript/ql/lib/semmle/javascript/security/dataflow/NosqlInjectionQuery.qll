/**
 * Provides a taint tracking configuration for reasoning about NoSQL
 * injection vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `NosqlInjection::Configuration` is needed, otherwise
 * `NosqlInjectionCustomizations` should be imported instead.
 */

import javascript
import semmle.javascript.security.TaintedObject
import NosqlInjectionCustomizations::NosqlInjection
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards
private import semmle.javascript.dataflow2.DeduplicateFlowState

module ConfigurationArgs implements DataFlow2::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  private predicate isSourceRaw(DataFlow::Node source, FlowState state) {
    source instanceof Source and state.isTaint()
    or
    TaintedObject::isSource(source, state)
  }

  private predicate isSinkRaw(DataFlow::Node sink, FlowState state) {
    sink.(Sink).getAFlowLabel() = state
  }

  import MakeDeduplicateFlowState<isSourceRaw/2, isSinkRaw/2>

  predicate isBarrier(DataFlow::Node node) { barrierGuardBlocksNode(node) }

  predicate isBarrier(DataFlow::Node node, FlowState state) {
    node instanceof Sanitizer and state.isTaint()
    or
    barrierGuardBlocksNode(node, state)
    or
    deduplicationBarrier(node, state)
  }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, FlowState state1, DataFlow::Node node2, FlowState state2
  ) {
    TaintedObject::step(node1, node2, state1, state2)
    or
    // additional flow step to track taint through NoSQL query objects
    state1 = TaintedObject::label() and
    state2 = TaintedObject::label() and
    exists(NoSql::Query query, DataFlow::SourceNode queryObj |
      queryObj.flowsTo(query) and
      queryObj.flowsTo(node2) and
      node1 = queryObj.getAPropertyWrite().getRhs()
    )
    or
    deduplicationStep(node1, state1, node2, state2)
  }

  private predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) {
    guard instanceof TaintedObject::SanitizerGuard
  }

  import MakeSanitizerGuards<isBarrierGuard/1>
}

module Configuration = TaintTracking2::GlobalWithState<ConfigurationArgs>;

/**
 * A taint-tracking configuration for reasoning about SQL-injection vulnerabilities.
 */
deprecated class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "NosqlInjection" }

  override predicate isSource(DataFlow::Node source) { source instanceof Source }

  override predicate isSource(DataFlow::Node source, DataFlow::FlowLabel label) {
    TaintedObject::isSource(source, label)
  }

  override predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel label) {
    sink.(Sink).getAFlowLabel() = label
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof Sanitizer
  }

  override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode guard) {
    guard instanceof TaintedObject::SanitizerGuard
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node node1, DataFlow::Node node2, DataFlow::FlowLabel state1,
    DataFlow::FlowLabel state2
  ) {
    ConfigurationArgs::isAdditionalFlowStep(node1, state1, node2, state2)
  }
}
