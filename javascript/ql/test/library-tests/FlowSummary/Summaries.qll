import javascript
import semmle.javascript.dataflow2.DataFlow as DataFlow2
import semmle.javascript.dataflow2.BarrierGuards
import semmle.javascript.dataflow2.FlowSummary

class MkSummary extends SummarizedCallable {
  private CallExpr mkSummary;

  MkSummary() {
    mkSummary.getCalleeName() = "mkSummary" and
    this =
      "mkSummary at " + mkSummary.getFile().getRelativePath() + ":" +
        mkSummary.getLocation().getStartLine()
  }

  override DataFlow::InvokeNode getACall() {
    result = mkSummary.flow().(DataFlow::CallNode).getAnInvocation()
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      // mkSummary(input, output)
      input = mkSummary.getArgument(0).getStringValue() and
      output = mkSummary.getArgument(1).getStringValue()
      or
      // mkSummary([
      //   [input1, output1],
      //   [input2, output2],
      //   ...
      // ])
      exists(ArrayExpr pair |
        pair = mkSummary.getArgument(0).(ArrayExpr).getAnElement() and
        input = pair.getElement(0).getStringValue() and
        output = pair.getElement(1).getStringValue()
      )
    )
  }
}
