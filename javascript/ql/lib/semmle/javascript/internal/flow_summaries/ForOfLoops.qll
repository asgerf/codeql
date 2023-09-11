/**
 * Contains flow steps to model flow through `for..of` loops.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.AdditionalFlowInternal

class ForOfLoopStep extends AdditionalFlowInternal {
  override predicate needsSynthesizedNode(AstNode node, string tag, StmtContainer container) {
    // Intermediate nodes to convert (MapKey, MapValue) to a `[key, value]` array.
    node instanceof ForOfStmt and
    tag = ["map-key", "map-value"] and
    container = node.getContainer()
  }

  override predicate readStep(
    DataFlow::Node pred, DataFlow::ContentSet contents, DataFlow::Node succ
  ) {
    exists(ForOfStmt stmt | pred = stmt.getIterationDomain().flow() |
      contents =
        [
          DataFlow::ContentSet::arrayElement(), DataFlow::ContentSet::setElement(),
          DataFlow::ContentSet::iteratorElement()
        ] and
      succ = DataFlow::lvalueNode(stmt.getLValue())
      or
      contents = DataFlow::ContentSet::mapKey() and
      succ = getSynthesizedNode(stmt, "map-key")
      or
      contents = DataFlow::ContentSet::mapValueAll() and
      succ = getSynthesizedNode(stmt, "map-value")
      or
      contents = DataFlow::ContentSet::iteratorError() and
      succ = stmt.getIterationDomain().getExceptionTarget()
    )
  }

  override predicate storeStep(
    DataFlow::Node pred, DataFlow::ContentSet contents, DataFlow::Node succ
  ) {
    exists(ForOfStmt stmt |
      pred = getSynthesizedNode(stmt, "map-key") and
      contents.asArrayIndex() = 0
      or
      pred = getSynthesizedNode(stmt, "map-value") and
      contents.asArrayIndex() = 1
    |
      succ = DataFlow::lvalueNode(stmt.getLValue())
    )
  }
}
