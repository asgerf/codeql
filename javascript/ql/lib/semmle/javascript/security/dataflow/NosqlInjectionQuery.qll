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

module ConfigurationArgs implements DataFlow::StateConfigSig {
  predicate isSource(DataFlow::Node source, DataFlow::FlowLabel state) {
    source instanceof Source and state.isTaint()
    or
    TaintedObject::isSource(source, state)
  }

  predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel state) {
    sink.(Sink).getAFlowLabel() = state
  }

  predicate isBarrier(DataFlow::Node node, DataFlow::FlowLabel state) {
    node instanceof Sanitizer and state.isTaint()
  }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, DataFlow::FlowLabel state1, DataFlow::Node node2,
    DataFlow::FlowLabel state2
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
  }

  predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) {
    guard instanceof TaintedObject::SanitizerGuard
  }
}

module Configuration = TaintTracking::GlobalWithState<ConfigurationArgs>;

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
