private import javascript
private import Stage1

/**
 * Flow rules for anything that causes flow into an L-value.
 */
class AssignmentFlow extends Stage1 {
  override predicate valueStep(Node node1, Node node2) {
    exists(VariableDeclarator decl |
      node1 = decl.getValue() and node2 = getLValueNode(decl.getName())
    )
    or
    exists(AssignmentExpression asn |
      node1 = asn.getRight() and
      node2 = [asn, getLValueNode(asn.getLeft())]
    )
    or
    exists(BinaryExpressionInAssignment expr |
      node1 = expr and
      node2 = getLValueNode(expr.getAssignment().getLeft())
    )
    or
    exists(ForInStatement stmt |
      // initialValue -> x in the extremely rare case:
      // for (var x = initialValue in foo(x)) { ... }
      node1 = stmt.getValue() and
      node2 = getLValueNode(stmt.getLeft())
    )
  }

  override predicate taintStep(Node node1, Node node2) {
    exists(ForInStatement stmt |
      stmt.getOperator() = "in" and
      node1 = stmt.getRight() and
      node2 = getLValueNode(stmt.getLeft())
    )
  }

  override predicate readStep(Node node1, ContentSet contents, Node node2) {
    exists(ForInStatement stmt |
      stmt.getOperator() = "of" and
      node1 = stmt.getRight() and
      contents.isAnyArrayElement() and
      node2 = getLValueNode(stmt.getLeft())
    )
  }
}
