private import javascript
private import semmle.javascript.dataflow2.FlowSummary

class ForEach extends SummarizedCallable {
  ForEach() { this = "Array#forEach" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = "forEach" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[this].ArrayElement" and
      output = "Argument[0].Parameter[0]"
    )
  }
}

class Push extends SummarizedCallable {
  Push() { this = "Array#push" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = "push" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[0]" and // TODO: support more arguments
    output = "Argument[this].ArrayElement"
  }
}

class Shift extends SummarizedCallable {
  Shift() { this = "Array#shift" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = "shift" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this].ArrayElement" and
    output = "ReturnValue"
  }
}
