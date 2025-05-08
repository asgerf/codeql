private import codeql.js.base.BaseLayer

module Conditions {
  predicate isCondition(AstNode node) {
    node = any(IfStatement s).getCondition()
    or
    node = any(WhileStatement s).getCondition()
    or
    node = any(DoStatement s).getCondition()
    or
    node = any(TernaryExpression e).getCondition()
    or
    exists(UnaryExpression unary |
      unary.getOperator() = "!" and
      node = unary.getArgument()
    )
    or
    exists(BinaryExpression binary |
      binary.getOperator() = ["&&", "||", "??"] and
      node = binary.getLeft()
    )
    or
    exists(AugmentedAssignmentExpression expr |
      expr.getOperator() = ["&&=", "||=", "??="] and
      node = expr.getLeft()
    )
    or
    node instanceof AssignmentPattern
    or
    // The `x` in `x?.foo` needs to be checked
    node = OptionalChaining::getImmediateOptionalChainRoot(_)
  }

  pragma[nomagic]
  SyntheticNode getThenOutcome(AstNode node) { result = node.getSyntheticChildNode("then-outcome") }

  pragma[nomagic]
  AstNode tryGetThenOutcome(AstNode node) {
    result = getThenOutcome(node)
    or
    not exists(getThenOutcome(node)) and result = node
  }

  pragma[nomagic]
  SyntheticNode getElseOutcome(AstNode node) { result = node.getSyntheticChildNode("else-outcome") }

  pragma[nomagic]
  AstNode tryGetElseOutcome(AstNode node) {
    result = getElseOutcome(node)
    or
    not exists(getElseOutcome(node)) and result = node
  }
}
