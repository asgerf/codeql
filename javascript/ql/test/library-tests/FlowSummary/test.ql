import javascript
import semmle.javascript.dataflow2.DataFlow as DataFlow2
import semmle.javascript.dataflow2.BarrierGuards
import semmle.javascript.dataflow2.FlowSummary
import testUtilities.ConsistencyChecking

DataFlow::CallNode getACall(string name) {
  result.getCalleeName() = name
  or
  result.getCalleeNode().getALocalSource() = DataFlow::globalVarRef(name)
}

module ConfigArg implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow::Node node) { node = getACall("source") }

  predicate isSink(DataFlow::Node node) { node = getACall("sink").getAnArgument() }

  predicate isBarrier(DataFlow::Node node) {
    node.(DataFlow::InvokeNode).getCalleeName().matches("sanitizer_%")
    or
    barrierGuardBlocksNode(node, _)
  }
}

module Configuration = DataFlow2::Global<ConfigArg>;

class BasicBarrierGuard extends DataFlow::BarrierGuardNode, DataFlow::CallNode {
  BasicBarrierGuard() { this = getACall("isSafe") }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and e = this.getArgument(0).asExpr()
  }
}

class ConsistencyConfig extends ConsistencyConfiguration {
  ConsistencyConfig() { this = "ConsistencyConfig" }

  override DataFlow::Node getAnAlert() { Configuration::flow(_, result) }
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
