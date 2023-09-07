private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.FlowSummary
private import semmle.javascript.dataflow2.AdditionalFlowInternal
private import FlowSummaryUtil

class AsyncAwait extends AdditionalFlowInternal {
  override predicate needsSynthesizedNode(AstNode node, string tag, StmtContainer container) {
    node.(Function).isAsync() and
    container = node and
    tag = "async-raw-return" // Node containing the value about to be boxed in a promise.
  }

  override predicate clearsContent(DataFlow::Node node, DataFlow2::ContentSet contents) {
    // Result of 'await' cannot be a promise; needed for the local flow step into 'await'
    node.asExpr() instanceof AwaitExpr and
    contents = DataFlow2::ContentSet::promiseFilter()
    or
    // Ensure the value about to be boxed in a promise can't be a promise
    node = getSynthesizedNode(_, "async-raw-return") and
    contents = DataFlow2::ContentSet::promiseFilter()
  }

  override predicate expectsContent(DataFlow::Node node, DataFlow2::ContentSet contents) {
    exists(Function f |
      f.isAsync() and
      node = TFunctionReturnNode(f) and
      contents = DataFlow2::ContentSet::promiseFilter()
    )
  }

  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(AwaitExpr await |
      // Allow non-promise values to propagate through await. The target node has clearsContent so promises can't pass through.
      pred = await.getOperand().flow() and
      succ = await.flow()
    )
    or
    exists(Function f |
      // To avoid creating a nested promise, flow to two different nodes which only permit promises/non-promises respectively
      f.isAsync() and
      pred = f.getAReturnedExpr().flow()
    |
      succ = getSynthesizedNode(f, "async-raw-return") // clears promise-content
      or
      succ = TFunctionReturnNode(f) // expects promise-content
    )
  }

  override predicate readStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    exists(AwaitExpr await | pred = await.getOperand().flow() |
      succ = await.flow() and
      content.asPropertyName() = Promises::valueProp()
      or
      succ = await.getExceptionTarget() and
      content.asPropertyName() = Promises::errorProp()
    )
  }

  override predicate storeStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    exists(Function f | f.isAsync() |
      pred = getSynthesizedNode(f, "async-raw-return") and
      succ = TFunctionReturnNode(f) and
      content.asPropertyName() = Promises::valueProp()
      or
      // Store thrown exceptions in the promise-error
      pred = TExceptionalFunctionReturnNode(f) and
      succ = TFunctionReturnNode(f) and
      content.asPropertyName() = Promises::errorProp()
    )
  }
}
