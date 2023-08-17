import javascript
import semmle.javascript.dataflow2.DataFlow as DataFlow2
import semmle.javascript.dataflow2.BarrierGuards
import semmle.javascript.dataflow2.FlowSummary

DataFlow::CallNode getACall(string name) {
  result.getCalleeName() = name
  or
  result.getCalleeNode().getALocalSource() = DataFlow::globalVarRef(name)
}

abstract class SimpleSummarizedCallable extends SummarizedCallable {
  bindingset[this]
  SimpleSummarizedCallable() { any() }

  override DataFlow::InvokeNode getACall() { result = getACall(this) }
}

class FlowThrough extends SimpleSummarizedCallable {
  FlowThrough() { this = "flowThrough" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowIntoProp extends SimpleSummarizedCallable {
  FlowIntoProp() { this = "flowIntoProp" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue.Member[prop]" and preservesValue = true
  }
}

class FlowOutOfProp extends SimpleSummarizedCallable {
  FlowOutOfProp() { this = "flowOutOfProp" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Member[prop]" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowIntoArrayElement extends SimpleSummarizedCallable {
  FlowIntoArrayElement() { this = "flowIntoArrayElement" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue.ArrayElement" and preservesValue = true
  }
}

class FlowIntoPromise extends SimpleSummarizedCallable {
  FlowIntoPromise() { this = "flowIntoPromise" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue.Awaited" and preservesValue = true
  }
}

class FlowOutOfPromise extends SimpleSummarizedCallable {
  FlowOutOfPromise() { this = "flowOutOfPromise" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Awaited" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowOutOfCallback extends SimpleSummarizedCallable {
  FlowOutOfCallback() { this = "flowOutOfCallback" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].ReturnValue" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowIntoCallback extends SimpleSummarizedCallable {
  FlowIntoCallback() { this = "flowIntoCallback" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "Argument[1].Parameter[0]" and preservesValue = true
  }
}

class FlowThroughCallback extends SimpleSummarizedCallable {
  FlowThroughCallback() { this = "flowThroughCallback" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "Argument[1].Parameter[0]" and preservesValue = true
    or
    input = "Argument[1].ReturnValue" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowOutOfInnerCallback extends SimpleSummarizedCallable {
  FlowOutOfInnerCallback() { this = "flowOutOfInnerCallback" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Parameter[0].Argument[0]" and
    output = "ReturnValue" and
    preservesValue = true
  }
}

class FlowFromSideEffectOnParameter extends SimpleSummarizedCallable {
  FlowFromSideEffectOnParameter() { this = "flowFromSideEffectOnParameter" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Parameter[0].Member[prop]" and
    output = "ReturnValue" and
    preservesValue = true
  }
}
