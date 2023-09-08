/**
 * Contains flow summaries and steps modelling flow through iterators.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.FlowSummary
private import semmle.javascript.dataflow2.AdditionalFlowInternal
private import FlowSummaryUtil

class IteratorNext extends SummarizedCallable {
  IteratorNext() { this = "Iterator#next" }

  override DataFlow::MethodCallNode getACallSimple() {
    result.getMethodName() = "next" and
    result.getNumArgument() = 0
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[this].IteratorElement" and
      output = "ReturnValue.Member[value]"
      or
      input = "Argument[this].IteratorError" and
      output = "ReturnValue[exception]"
    )
  }
}
