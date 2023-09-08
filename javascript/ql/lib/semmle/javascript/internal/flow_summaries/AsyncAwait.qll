/**
 * Contains flow steps to model flow through `async` functions and the `await` operator.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.AdditionalFlowInternal

/**
 * Steps modelling flow in an `async` function.
 *
 * Note about promise-coercion and flattening:
 * - `await` preserves non-promise values, e.g. `await "foo"` is just `"foo"`.
 * - `return` preserves existing promise values, and boxes other values in a promise.
 *
 * We rely on `expectsContent` and `clearsContent` to handle coercion/flattening without risk of creating a nested promise object.
 *
 * The following is a brief overview of the steps we generate:
 * ```js
 * async function foo() {
 *   await x;  // x --- READ[promise-value] ---> await x
 *   await x;  // x --- VALUE -----------------> await x (has clearsContent)
 *   await x;  // x --- READ[promise-error] ---> exception target
 *
 *   return x; // x --- VALUE --> return node (has expectsContent)
 *   return x; // x --- VALUE --> synthetic node (clearsContent) --- STORE[promise-value] --> return node
 *
 *   // exceptional return node --> STORE[promise-error] --> return node
 * }
 * ```
 */
class AsyncAwait extends AdditionalFlowInternal {
  override predicate needsSynthesizedNode(AstNode node, string tag, StmtContainer container) {
    // We synthesize a clearsContent node to contain the values that need to be boxed in a promise before returning
    node.(Function).isAsync() and
    container = node and
    tag = "async-raw-return"
  }

  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(AwaitExpr await |
      // Allow non-promise values to propagate through await.
      pred = await.getOperand().flow() and
      succ = await.flow() // clears promise-content
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
      // Box returned non-promise values in a promise
      pred = getSynthesizedNode(f, "async-raw-return") and
      content.asPropertyName() = Promises::valueProp() and
      succ = TFunctionReturnNode(f)
      or
      // Store thrown exceptions in promise-error
      pred = TExceptionalFunctionReturnNode(f) and
      content.asPropertyName() = Promises::errorProp() and
      succ = TFunctionReturnNode(f)
    )
  }

  override predicate clearsContent(DataFlow::Node node, DataFlow2::ContentSet contents) {
    // Result of 'await' cannot be a promise. This is needed for the local flow step into 'await'
    node.asExpr() instanceof AwaitExpr and
    contents = DataFlow2::ContentSet::promiseFilter()
    or
    // Ensure the value about to be boxed in a promise can't be a promise
    node = getSynthesizedNode(_, "async-raw-return") and
    contents = DataFlow2::ContentSet::promiseFilter()
  }

  override predicate expectsContent(DataFlow::Node node, DataFlow2::ContentSet contents) {
    // The final return value must be a promise. This is needed for the local flow step into the return node.
    exists(Function f |
      f.isAsync() and
      node = TFunctionReturnNode(f) and
      contents = DataFlow2::ContentSet::promiseFilter()
    )
  }
}
