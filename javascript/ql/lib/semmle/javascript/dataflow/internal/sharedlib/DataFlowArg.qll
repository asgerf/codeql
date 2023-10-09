private import DataFlowImplSpecific
private import codeql.dataflow.DataFlow as SharedDataFlow
private import codeql.dataflow.TaintTracking as SharedTaintTracking

module JSDataFlow implements SharedDataFlow::InputSig {
  import Private
  import Public

  // Explicitly implement signature members that have a default
  predicate typeStrongerThan = Private::typeStrongerThan/2;

  predicate neverSkipInPathGraph = Private::neverSkipInPathGraph/1;

  predicate accessPathLimit = Private::accessPathLimit/0;
}

module JSTaintFlow implements SharedTaintTracking::InputSig<JSDataFlow> {
  import semmle.javascript.dataflow.internal.TaintTrackingPrivate
}
