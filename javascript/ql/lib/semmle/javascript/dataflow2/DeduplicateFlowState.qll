/**
 * A helper module for configuring flow state in a way that avoids
 * duplicate source/sinks pairs that only differ by their flow state.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2

string sourceState() { result = "SourceState" }

string sinkState() { result = "SinkState" }

private class SourceState extends DataFlow::FlowLabel {
  SourceState() { this = sourceState() }
}

private class SinkState extends DataFlow::FlowLabel {
  SinkState() { this = sinkState() }
}

signature predicate nodeAndFlowState(DataFlow::Node node, DataFlow::FlowLabel label);

module MakeDeduplicateFlowState<nodeAndFlowState/2 sources, nodeAndFlowState/2 sinks> {
  predicate isSource(DataFlow::Node node, DataFlow::FlowLabel state) {
    sources(node, _) and
    state = sourceState()
  }

  predicate isSink(DataFlow::Node node, DataFlow::FlowLabel state) {
    sinks(node, _) and
    state = sinkState()
  }

  predicate deduplicationStep(
    DataFlow::Node node1, DataFlow::FlowLabel state1, DataFlow::Node node2,
    DataFlow::FlowLabel state2
  ) {
    exists(DataFlow::Node source |
      node1 = source and
      node2 = source and
      state1 = sourceState() and
      sources(source, state2)
    )
    or
    exists(DataFlow::Node sink |
      node1 = sink and
      node2 = sink and
      sinks(sink, state1) and
      state2 = sinkState()
    )
  }
}
