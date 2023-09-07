/**
 * Contains flow summaries and steps to model `for..of` loops, generators, and iterators.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.FlowSummary
private import FlowSummaryUtil

class ForOfLoopStep extends DataFlow::AdditionalFlowStep {
  override predicate readStep(
    DataFlow::Node pred, DataFlow2::ContentSet contents, DataFlow::Node succ
  ) {
    exists(ForOfStmt stmt | pred = stmt.getIterationDomain().flow() |
      contents =
        [
          DataFlow2::ContentSet::arrayElement(), DataFlow2::ContentSet::setElement(),
          DataFlow2::ContentSet::iteratorElement()
        ] and
      succ = DataFlow::lvalueNode(stmt.getLValue())
      or
      contents = DataFlow2::ContentSet::mapKey() and
      succ = TForOfSyntheticPairNode(stmt, 0)
      or
      contents = DataFlow2::ContentSet::mapValueAll() and
      succ = TForOfSyntheticPairNode(stmt, 1)
      or
      contents = DataFlow2::ContentSet::iteratorError() and
      succ = stmt.getIterationDomain().getExceptionTarget()
    )
  }

  override predicate storeStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    exists(ForOfStmt stmt, int i |
      pred = TForOfSyntheticPairNode(stmt, i) and
      content.asPropertyName() = i.toString() and
      succ = DataFlow::lvalueNode(stmt.getLValue())
    )
  }
}

class GeneratorFunctionStep extends DataFlow::AdditionalFlowStep {
  override predicate storeStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    // `yield x`. Store into the return value's iterator element.
    exists(Function fun, YieldExpr yield | fun.isGenerator() |
      not yield.isDelegating() and
      yield.getContainer() = fun and
      pred = yield.getOperand().flow() and
      content = DataFlow2::ContentSet::iteratorElement() and
      DataFlow::functionReturnNode(succ, fun)
    )
  }

  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    // `yield* x`. Flow into the return value, which has expectsContent, so only iterator contents can pass through.
    exists(Function fun, YieldExpr yield |
      fun.isGenerator() and
      yield.getContainer() = fun and
      yield.isDelegating() and
      pred = yield.getOperand().flow() and
      DataFlow::functionReturnNode(succ, fun)
    )
  }
}

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
