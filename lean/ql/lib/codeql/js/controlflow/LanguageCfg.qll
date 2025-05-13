private import All
private import codeql.shared.LanguageCfg::ControlFlow<Location, LanguageBase, LanguageCommon>
private import ValueFilter

/**
 * An explicit step from `node1` to `node2`.
 *
 * The existence of an explicit step `node1 -> node2` suppresses the default left-to-right edge out of `node1` and
 * as well as the default left-to-right edge into `node2`.
 */
pragma[nomagic]
predicate explicitStep(CfgNode1 node1, CfgNode2 node2) {
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
  exists(ForStatement stmt |
    node1.isAfter(stmt.getInitializer()) and
    node2.isBefore([stmt.getCondition(0), stmt.getSyntheticChildNode("empty-condition")])
    or
    node1.isAfterTrue([stmt.getCondition(0), stmt.getSyntheticChildNode("empty-condition")]) and
    node2.isBefore(stmt.getBody())
    or
    node1.isAfterFalse([stmt.getCondition(0), stmt.getSyntheticChildNode("empty-condition")]) and
    node2.isAfter(stmt)
    or
    node1.isAfter(stmt.getBody()) and
    node2.isBefore([stmt.getIncrement(), stmt.getSyntheticChildNode("empty-increment")])
    or
    node1.isAfter([stmt.getIncrement(), stmt.getSyntheticChildNode("empty-increment")]) and
    node2.isBefore(stmt.getBody())
  )
  or
  exists(ForInStatement stmt |
    node1.isBefore(stmt) and
    node2.isBefore(stmt.getRight())
    or
    node1.isAfter(stmt.getRight()) and
    node2 = stmt.getSyntheticChildNode("loop-header")
    or
    node1 = stmt.getSyntheticChildNode("loop-header") and
    node2.isBefore(stmt.getLeft()) // Visit 'left' inside the loop. `for (g().x in y)` will cause `g()` to be called in every iteration.
    or
    node1.isAfter(stmt.getLeft()) and
    node2.isBeforeAssigningTo(stmt.getLeft())
    or
    node1.isAfterAssigningTo(stmt.getLeft()) and
    node2.isBefore(stmt.getBody())
    or
    node1.isAfter(stmt.getBody()) and
    node2 = stmt.getSyntheticChildNode("loop-header")
    or
    node1 = stmt.getSyntheticChildNode("loop-header") and
    node2.isAfter(stmt)
  )
  or
  exists(AssignmentPattern pattern |
    node1.isBeforeAssigningTo(pattern, TNotNullLike()) and
    node2.isBeforeAssigningTo(pattern.getLeft())
    or
    node1.isBeforeAssigningTo(pattern, TNullLike()) and
    node2.isBefore(pattern.getRight())
    or
    node1.isAfter(pattern.getRight()) and
    node2.isBeforeAssigningTo(pattern.getLeft())
  )
  or
  exists(BinaryExpression binary, ValueFilter shortCircuit |
    shortCircuit = getShortCircuitingCondition(binary.getOperator())
  |
    node1.isAfter(binary.getLeft(), shortCircuit) and
    node2.isAfter(binary, shortCircuit)
    or
    node1.isAfter(binary.getLeft(), shortCircuit.negate()) and
    node2.isBefore(binary.getRight())
    or
    propagateExactly(binary.getRight(), binary, node1, node2)
  )
  or
  exists(AugmentedAssignmentExpression assign, ValueFilter shortCircuit |
    shortCircuit = getShortCircuitingCondition(assign.getOperator())
  |
    node1.isAfter(assign.getLeft(), shortCircuit) and
    node2.isAfter(assign, shortCircuit)
    or
    node1.isAfter(assign.getLeft(), shortCircuit.negate()) and
    node2.isBefore(assign.getRight())
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
  exists(TernaryExpression expr |
    node1.isAfterTrue(expr.getCondition()) and
    node2.isBefore(expr.getConsequence())
    or
    node1.isAfterFalse(expr.getCondition()) and
    node2.isBefore(expr.getAlternative())
    or
    propagateExactly([expr.getConsequence(), expr.getAlternative()], expr, node1, node2)
  )
  or
  exists(OptionalMemberExpression expr |
    node1.isAfter(expr.getObject(), TNotNullLike()) and
    node2.isAfter(expr)
    or
    node1.isAfter(expr.getObject(), TNullLike()) and
    node2.isAfter(expr.getOutermostAccessor(), TNullLike())
  )
  or
  exists(OptionalSubscriptExpression expr |
    node1.isAfter(expr.getObject(), TNotNullLike()) and
    node2.isBefore(expr.getIndex())
    or
    node1.isAfter(expr.getObject(), TNullLike()) and
    node2.isAfter(expr.getOutermostAccessor(), TNullLike())
  )
  or
  exists(OptionalCallExpression expr |
    node1.isAfter(expr.getFunction(), TNotNullLike()) and
    node2.isBefore(expr.getArguments())
    or
    node1.isAfter(expr.getFunction(), TNullLike()) and
    node2.isAfter(expr.getOutermostAccessor(), TNullLike())
  )
  or
  exists(VariableDeclarator decl |
    (
      node1.isAfter(decl.getValue())
      or
      not exists(decl.getValue()) and
      node1.isBefore(decl.getName())
    ) and
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
  or
  exists(LogicalNot expr |
    node1.isAfterTrue(expr.getArgument()) and
    node2.isAfterFalse(expr)
    or
    node1.isAfterFalse(expr.getArgument()) and
    node2.isAfterTrue(expr)
  )
  or
  exists(ParenthesizedExpression expr | propagateExactly(expr.getChild(), expr, node1, node2))
}

import MakeCfg<explicitStep/2> as Cfg

private module Consistency {
  import Cfg::Debug
}

bindingset[expr1, expr2]
pragma[inline_late]
private predicate propagateExactly(AstNode expr1, AstNode expr2, CfgNode1 node1, CfgNode2 node2) {
  exists(ValueFilter filter | filter = getConditionFilter(expr2) |
    node1.isAfter(expr1, filter) and
    node2.isAfter(expr2, filter)
    or
    node1.isAfter(expr1, filter.negate()) and
    node2.isAfter(expr2, filter.negate())
  )
  or
  not exists(getConditionFilter(expr2)) and
  node1.isAfter(expr1) and
  node2.isAfter(expr2)
}
