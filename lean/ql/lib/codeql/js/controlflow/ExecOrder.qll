private import javascript
private import codeql.js.controlflow.ControlFlowShared
private import ValueFilter
private import OptionalChaining

private class CfgNode extends AstNode {
  // Set bindingset to help catch missing bindings
  bindingset[this]
  CfgNode() { any() }

  predicate isBefore(AstNode node) { this = node.getSyntheticChildNode("begin") }

  predicate isAfter(AstNode node) { this = node }

  predicate isAfterTrue(AstNode node) {
    Conditions::isCondition(node) and
    this = node.getSyntheticChildNode("true-outcome")
  }

  predicate isAfterFalse(AstNode node) {
    Conditions::isCondition(node) and
    this = node.getSyntheticChildNode("false-outcome")
  }

  predicate isAfterShortCircuit(AstNode node) { this.isAfterTrue(node) }

  predicate isAfterNoShortCircuit(AstNode node) { this.isAfterFalse(node) }

  predicate isBeforeAssigningTo(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue") }

  predicate isBeforeAssigningToTrue(AstNode lvalue) {
    this = lvalue.getSyntheticChildNode("lvalue-true")
  }

  predicate isBeforeAssigningToFalse(AstNode lvalue) {
    this = lvalue.getSyntheticChildNode("lvalue-false")
  }

  predicate isAfterAssigningTo(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue-end") }
}

pragma[nomagic]
predicate succ(CfgNode node1, CfgNode node2) {
  exists(IfStatement stmt |
    node1.isAfterTrue(stmt.getCondition()) and
    node2.isBefore(stmt.getConsequence())
    or
    node1.isAfterFalse(stmt.getCondition()) and
    (
      node2.isBefore(stmt.getAlternative().getChild())
      or
      not exists(stmt.getAlternative()) and
      node2.isAfter(stmt)
    )
    or
    node1.isAfter(stmt.getConsequence()) and
    node2.isAfter(stmt)
    or
    node1.isAfter(stmt.getAlternative().getChild()) and
    node2.isAfter(stmt)
  )
  or
  exists(WhileStatement stmt |
    node1.isBefore(stmt) and
    node2.isBefore(stmt.getCondition())
    or
    node1.isAfterTrue(stmt.getCondition()) and
    node2.isBefore(stmt.getBody())
    or
    node1.isAfterFalse(stmt.getCondition()) and
    node2.isAfter(stmt)
    or
    node1.isAfter(stmt.getBody()) and
    node2.isBefore(stmt.getCondition())
  )
  or
  exists(DoStatement stmt |
    node1.isBefore(stmt) and
    node2.isBefore(stmt.getBody())
    or
    node1.isAfter(stmt.getBody()) and
    node2.isBefore(stmt.getCondition())
    or
    node1.isAfterTrue(stmt.getCondition()) and
    node2.isBefore(stmt.getBody())
    or
    node1.isAfterFalse(stmt.getCondition()) and
    node2.isAfter(stmt)
  )
  or
  exists(ForStatement stmt |
    node1.isBefore(stmt) and
    node2.isBefore(stmt.getInitializer())
    or
    node1.isAfter(stmt.getInitializer()) and
    node2.isBefore(stmt.getCondition(0))
    or
    node1.isAfterTrue(stmt.getCondition(0)) and
    node2.isBefore(stmt.getBody())
    or
    node1.isAfterFalse(stmt.getCondition(0)) and
    node2.isAfter(stmt)
    or
    node1.isAfter(stmt.getBody()) and
    node2.isBefore(stmt.getIncrement())
    or
    node1.isAfter(stmt.getIncrement()) and
    node2.isBefore(stmt.getCondition(0))
  )
  or
  exists(ForInStatement stmt |
    node1.isBefore(stmt) and
    node2.isBefore(stmt.getRight())
    or
    node1.isAfter(stmt.getRight()) and
    node2.isBefore(stmt.getSyntheticChildNode("loop-header"))
    or
    node1.isAfter(stmt.getSyntheticChildNode("loop-header")) and
    node2.isBefore(stmt.getLeft())
    or
    node1.isAfter(stmt.getLeft()) and
    node2.isBeforeAssigningTo(stmt.getLeft())
    or
    node1.isAfterAssigningTo(stmt.getLeft()) and
    node2.isBefore(stmt.getBody())
  )
  or
  exists(AssignmentPattern pattern |
    node1.isBeforeAssigningToTrue(pattern) and
    node2.isBeforeAssigningTo(pattern.getLeft())
    or
    node1.isBeforeAssigningToFalse(pattern) and
    node2.isBefore(pattern.getRight())
    or
    node1.isAfter(pattern.getRight()) and
    node2.isBeforeAssigningTo(pattern.getLeft())
  )
  or
  exists(BinaryExpression binary | binary.getOperator() = ["&&", "||", "??"] |
    node1.isAfterShortCircuit(binary.getLeft()) and
    node2.isAfterFalse(binary)
    or
    node1.isAfterNoShortCircuit(binary.getLeft()) and
    node2.isBefore(binary.getRight())
    or
    node1.isAfter(binary.getRight()) and
    node2.isAfter(binary)
  )
  or
  exists(AugmentedAssignmentExpression assign | assign.getOperator() = ["&&=", "||=", "??="] |
    node1.isAfterShortCircuit(assign.getLeft()) and
    node2.isBefore(assign.getRight())
    or
    node1.isAfterFalse(assign.getLeft()) and
    node2.isAfterFalse(assign)
    or
    node1.isAfter(assign.getRight()) and
    node2 = assign.getSyntheticChildNode("binary-operator")
    or
    node1 = assign.getSyntheticChildNode("binary-operator") and
    node2.isBeforeAssigningTo(assign.getLeft())
    or
    node1.isAfterAssigningTo(assign.getLeft()) and
    node2.isAfter(assign)
  )
  or
  exists(AugmentedAssignmentExpression assign | not assign.getOperator() = ["&&=", "||=", "??="] |
    node1.isAfter(assign.getRight()) and
    node2 = assign.getSyntheticChildNode("binary-operator")
    or
    node1 = assign.getSyntheticChildNode("binary-operator") and
    node2.isBeforeAssigningTo(assign.getLeft())
    or
    node1.isAfterAssigningTo(assign.getLeft()) and
    node2.isAfter(assign)
  )
  or
  exists(OptionalMemberExpression expr |
    node1.isAfterTrue(expr.getObject()) and
    node2.isAfter(expr)
    or
    node1.isAfterFalse(expr.getObject()) and
    node2.isAfter(expr.getOutermostAccessor())
  )
  or
  exists(OptionalSubscriptExpression expr |
    node1.isAfterTrue(expr.getObject()) and
    node2.isBefore(expr.getIndex())
    or
    node1.isAfterFalse(expr.getObject()) and
    node2.isAfter(expr.getOutermostAccessor())
  )
  or
  exists(OptionalCallExpression expr |
    node1.isAfterTrue(expr.getFunction()) and
    node2.isBefore(expr.getArguments())
    or
    node1.isAfterFalse(expr.getFunction()) and
    node2.isAfter(expr.getOutermostAccessor())
  )
  or
  exists(VariableDeclarator decl |
    node1.isAfter(decl.getValue()) and
    node2.isBeforeAssigningTo(decl.getName())
    or
    node1.isAfterAssigningTo(decl.getName()) and
    node2.isAfter(decl)
  )
  or
  exists(AssignmentExpression expr |
    node1.isAfter(expr.getRight()) and
    node2.isBeforeAssigningTo(expr.getLeft())
    or
    node1.isAfterAssigningTo(expr.getLeft()) and
    node2.isAfter(expr)
  )
  or
  exists(UpdateExpression expr |
    node1.isAfter(expr.getArgument()) and
    node2.isBeforeAssigningTo(expr.getArgument())
    or
    node1.isAfterAssigningTo(expr.getArgument()) and
    node2.isAfter(expr)
  )
}

module Debug {
  predicate missingFlowIntoLValue(Node node) {
    LeftHandValues::isInLValuePosition(node) and
    not succ(_, getLValueNode(node))
  }
}
