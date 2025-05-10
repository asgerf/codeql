private import All
private import codeql.util.Unit

class Node = AstNode;

/**
 * Flow steps contributed to stage 1.
 */
class Stage1 extends Unit {
  predicate valueStep(Node node1, Node node2) { none() }

  predicate taintStep(Node node1, Node node2) { none() } // TODO: do we need taint steps in stage1?

  predicate readStep(Node node1, ContentSet contents, Node node2) { none() }

  predicate storeStep(Node node1, ContentSet contents, Node node2) { none() }

  predicate clearsContent(Node node1, ContentSet contents) { none() }

  predicate expectsContent(Node node1, ContentSet contents) { none() }
}
