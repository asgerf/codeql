private import DataFlowImplSpecific
private import codeql.dataflow.DataFlow
private import codeql.dataflow.TaintTracking as TT

module JSDataFlow implements InputSig {
  import Private
  import Public

  predicate typeStrongerThan(DataFlowType t1, DataFlowType t2) { none() }

  predicate neverSkipInPathGraph = Private::neverSkipInPathGraph/1;

  predicate accessPathLimit = Private::accessPathLimit/0;
}

module JSTaintFlow implements TT::InputSig<JSDataFlow> {
  private import Private
  private import Public

  /**
   * Holds if `node` should be a sanitizer in all global taint flow configurations
   * but not in local taint.
   */
  predicate defaultTaintSanitizer(Node node) { none() }

  /**
   * Holds if default `TaintTracking::Configuration`s should allow implicit reads
   * of `c` at sinks and inputs to additional taint steps.
   */
  bindingset[node]
  predicate defaultImplicitTaintRead(Node node, ContentSet c) { none() }

  predicate defaultAdditionalTaintStep = Private::defaultAdditionalTaintStep/2;
}
