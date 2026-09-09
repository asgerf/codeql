private import unified
private import AllDataFlow
private import codeql.dataflow.internal.DataFlowImplConsistency

module ConsistencyInput implements InputSig<Location, DataFlowInput> { }

module ConsistencyOutput =
  MakeConsistency<Location, DataFlowInput, TaintTrackingInput, ConsistencyInput>;
