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
  SyntheticNode getOutcome(AstNode node, string kind) {
    kind = ["true-outcome", "false-outcome"] and
    isCondition(node) and
    result = node.getSyntheticChildNode(kind)
  }

  pragma[nomagic]
  SyntheticNode getTrueOutcome(AstNode node) { result = getOutcome(node, "true-outcome") }

  pragma[nomagic]
  AstNode tryGetTrueOutcome(AstNode node) {
    result = getTrueOutcome(node)
    or
    not exists(getTrueOutcome(node)) and result = node
  }

  pragma[nomagic]
  SyntheticNode getFalseOutcome(AstNode node) { result = getOutcome(node, "false-outcome") }

  pragma[nomagic]
  AstNode tryGetFalseOutcome(AstNode node) {
    result = getFalseOutcome(node)
    or
    not exists(getFalseOutcome(node)) and result = node
  }
}
