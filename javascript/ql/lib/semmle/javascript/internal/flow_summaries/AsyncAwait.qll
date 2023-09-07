private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.FlowSummary
private import semmle.javascript.dataflow2.AdditionalFlowInternal
private import FlowSummaryUtil

class AsyncAwait extends AdditionalFlowInternal {
  override predicate clearsContent(DataFlow::Node node, DataFlow2::ContentSet contents) {
    // Result of 'await' cannot be a promise; needed for the local flow step into 'await'
    node.asExpr() instanceof AwaitExpr and
    contents = DataFlow2::ContentSet::promiseFilter()
    or
    // TODO: convert to synthesized node
    node = TAsyncFunctionIntermediateStoreReturnNode(_) and
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
      f.isAsync() and
      pred = f.getAReturnedExpr().flow()
    |
      succ = TAsyncFunctionIntermediateStoreReturnNode(f) // clears promise-content
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
      pred = TAsyncFunctionIntermediateStoreReturnNode(f) and
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
