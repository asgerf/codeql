import javascript
import semmle.javascript.dataflow2.DataFlow as DataFlow2
import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
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

module Configuration = TaintTracking2::Global<ConfigArg>;

class BasicSanitizerGuard extends TaintTracking::SanitizerGuardNode, DataFlow::CallNode {
  BasicSanitizerGuard() { this = getACall("isSafe") }

  override predicate sanitizes(boolean outcome, Expr e) {
    outcome = true and e = this.getArgument(0).asExpr()
  }
}

class ConsistencyConfig extends ConsistencyConfiguration {
  ConsistencyConfig() { this = "ConsistencyConfig" }

  override DataFlow::Node getAnAlert() { Configuration::flow(_, result) }
}

class FlowThrough extends SummarizedCallable {
  FlowThrough() { this = "flowThrough" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowThrough") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowThroughTaint extends SummarizedCallable {
  FlowThroughTaint() { this = "flowThroughTaint" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowThroughTaint") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue" and preservesValue = false
  }
}

class FlowIntoProp extends SummarizedCallable {
  FlowIntoProp() { this = "flowIntoProp" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowIntoProp") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue.Member[prop]" and preservesValue = true
  }
}

class FlowOutOfProp extends SummarizedCallable {
  FlowOutOfProp() { this = "flowOutOfProp" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowOutOfProp") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Member[prop]" and output = "ReturnValue" and preservesValue = true
  }
}

class FlowIntoArrayElement extends SummarizedCallable {
  FlowIntoArrayElement() { this = "flowIntoArrayElement" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowIntoArrayElement") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue.ArrayElement" and preservesValue = true
  }
}

class FlowIntoPromise extends SummarizedCallable {
  FlowIntoPromise() { this = "flowIntoPromise" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowIntoPromise") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and output = "ReturnValue.Awaited" and preservesValue = true
  }
}

class FlowOutOfPromise extends SummarizedCallable {
  FlowOutOfPromise() { this = "flowOutOfPromise" }

  override DataFlow::InvokeNode getACall() { result = getACall("flowOutOfPromise") }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0].Awaited" and output = "ReturnValue" and preservesValue = true
  }
}
