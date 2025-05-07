private import javascript

module ControlFlow {
  /** Edges that act as both control flow and data flow edges. */
  private predicate controlExpressionFlow1(Node node1, Node node2) {
    exists(BinaryExpressionLike expr | expr.getOperator() = ["||", "??"] |
      node1 = Conditions::getTrueOutcome(expr.getLeft()) and
      node2 = Conditions::tryGetTrueOutcome(expr)
      or
      node1 = expr.getRight() and
      node2 = expr
    )
    or
    exists(BinaryExpressionLike expr | expr.getOperator() = "&&" |
      node1 = Conditions::getFalseOutcome(expr.getLeft()) and
      node2 = Conditions::tryGetFalseOutcome(expr)
      or
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

  /** Edges that act as both control flow and data flow edges. */
  predicate controlExpressionFlow(Node node1, Node node2) {
    controlExpressionFlow1(node1, node2)
    or
    // For flow between a pair of non-synthetic nodes, also connect the corresponding
    // {true,false} outcome nodes if they exist. This only happens when a condition is nested
    // in another condition.
    exists(Node n1, Node n2 | controlExpressionFlow1(n1, n2) |
      node1 = Conditions::getTrueOutcome(n1) and
      node2 = Conditions::getTrueOutcome(n2)
      or
      node1 = Conditions::getFalseOutcome(n1) and
      node2 = Conditions::getFalseOutcome(n2)
    )
    or
    // Add flow from {true,false} to {false,true} through a negation operator
    exists(UnaryExpression unary | unary.getOperator() = "!" |
      node1 = Conditions::getTrueOutcome(unary.getArgument()) and
      node2 = Conditions::getFalseOutcome(unary)
      or
      node1 = Conditions::getFalseOutcome(unary.getArgument()) and
      node2 = Conditions::getTrueOutcome(unary)
    )
  }

  private predicate simpleBranch(Node condition, Node trueCase, Node falseCase, Node exitNode) {
    exists(IfStatement stmt |
      condition = stmt.getCondition() and
      trueCase = stmt.getConsequence() and
      (
        falseCase = stmt.getAlternative()
        or
        falseCase = stmt
      ) and
      exitNode = stmt
    )
    or
    exists(WhileStatement stmt |
      condition = stmt.getCondition() and
      trueCase = stmt.getBody() and
      falseCase = stmt and
      exitNode = stmt
    )
    or
    exists(DoStatement stmt |
      condition = stmt.getCondition() and
      trueCase = stmt.getBody() and
      falseCase = stmt and
      exitNode = stmt
    )
    or
    exists(ForStatement stmt |
      condition = stmt.getCondition(0) and
      trueCase = stmt.getBody() and
      falseCase = stmt and
      exitNode = stmt
    )
    or
    exists(ForInStatement stmt |
      condition = stmt.getSyntheticChildNode("loop-header") and
      trueCase = stmt.getBody() and
      falseCase = stmt and
      exitNode = stmt
    )
    or
    exists(OptionalChaining::OptionalChainExpression optionalChain |
      condition = optionalChain.getRoot() and
      trueCase = optionalChain.getFirstAccessor() and
      falseCase = optionalChain and
      exitNode = optionalChain
    )
  }

  private Node getFirst(Node node) { none() }

  bindingset[node, exitNode]
  private Node getFirstOrExit(Node node, Node exitNode) {
    if node = exitNode then result = exitNode else result = getFirst(node)
  }

  private predicate branchStep(Node node1, Node node2) {
    controlExpressionFlow(node1, node2)
    or
    exists(Node condition, Node trueCase, Node falseCase, Node exitNode |
      simpleBranch(condition, trueCase, falseCase, exitNode)
    |
      node1 = Conditions::getTrueOutcome(condition) and
      node2 = getFirstOrExit(trueCase, exitNode)
      or
      node1 = Conditions::getFalseOutcome(condition) and
      node2 = getFirstOrExit(falseCase, exitNode)
      or
      node1 = trueCase and
      node2 = exitNode
      or
      node1 = falseCase and
      node2 = exitNode
    ) and
    node1 != node2
  }
}
