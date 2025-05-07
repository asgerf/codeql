private import javascript
private import Stage1

class BasicFlow extends Stage1 {
  override predicate valueStep(Node node1, Node node2) {
    exists(BinaryExpressionLike expr |
      expr.getOperator() = ["||", "??"] and
      node1 = [expr.getLeft(), expr.getRight()] and
      node2 = expr
      or
      expr.getOperator() = "&&" and
      node1 = expr.getRight() and
      node2 = expr
    )
    or
    exists(TernaryExpression expr |
      node1 = [expr.getConsequence(), expr.getAlternative()] and
      node2 = expr
    )
    or
    exists(ParenthesizedExpression expr |
      node1 = expr.getChild() and
      node2 = expr
    )
  }

  override predicate taintStep(Node node1, Node node2) {
    exists(BinaryExpressionLike expr |
      expr.getOperator() = "+" and
      node1 = [expr.getLeft(), expr.getRight()] and
      node2 = expr
    )
    or
    exists(TemplateString expr |
      node1 = expr.getChild(_) and
      node2 = expr
    )
    or
    exists(TemplateSubstitution expr |
      node1 = expr.getChild() and
      node2 = expr
    )
  }

  override predicate readStep(Node node1, ContentSet contents, Node node2) {
    exists(PropAccess expr, Node key |
      node1 = expr.getObject() and
      node2 = expr and
      key = expr.getPropertyNameNode()
    |
      contents = getContentSetFromKey(key)
      or
      not exists(getContentSetFromKey(key)) and
      contents.isAnyArrayElement()
    )
  }
}
