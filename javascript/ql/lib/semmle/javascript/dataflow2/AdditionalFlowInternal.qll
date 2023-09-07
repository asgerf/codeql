private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.DataFlowImplSpecific
private import semmle.javascript.dataflow.internal.DataFlowNode

/**
 * Gets a data-flow node synthesized using `AdditionalFlowInternal#needsSynthesizedNode`.
 */
DataFlow::Node getSynthesizedNode(AstNode node, string tag) {
  result = TGenericSynthesizedNode(node, tag, _)
}

/**
 * An extension to `AdditionalFlowStep` with additional internal-only predicates.
 */
class AdditionalFlowInternal extends DataFlow::AdditionalFlowStep {
  /**
   * Holds if a data-flow node should be synthesized for the pair `(node, tag)`.
   *
   * The node can be obtained using `getSynthesizedNode(node, tag)`.
   *
   * `container` will be seen as the node's enclosing container.
   */
  predicate needsSynthesizedNode(AstNode node, string tag, StmtContainer container) { none() }

  /**
   * Holds if `node` should only permit flow of values stored in `contents`.
   */
  predicate expectsContent(DataFlow::Node node, DataFlow2::ContentSet contents) { none() }

  /**
   * Holds if `node` should not permit flow of values stored in `contents`.
   */
  predicate clearsContent(DataFlow::Node node, DataFlow2::ContentSet contents) { none() }
}
