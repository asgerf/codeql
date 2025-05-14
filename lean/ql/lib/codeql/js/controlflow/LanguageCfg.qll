private import All
private import codeql.shared.LanguageCfg::ControlFlow<Location, LanguageBase, LanguageCommon>
private import ValueFilter

private module ControlFlowGraphInput implements ControlFlowGraphSig {
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
      node1.isBefore(stmt) and
      node2.isBefore(stmt.getInitializer())
      or
      node1.isAfter(stmt.getInitializer()) and
      node2.isBefore([stmt.getCondition(0), stmt.getSyntheticChildNode("empty-condition")])
      or
      node1.isAfterTrue([stmt.getCondition(0), stmt.getSyntheticChildNode("empty-condition")]) and
      node2.isBefore(stmt.getBody())
      or
      node1.isAfterFalse(stmt.getCondition(0)) and // Note: omit the 'empty-condition' node here as it is always true
      node2.isAfter(stmt)
      or
      node1.isAfter(stmt.getBody()) and
      node2.isBefore([stmt.getIncrement(), stmt.getSyntheticChildNode("empty-increment")])
      or
      node1.isAfter([stmt.getIncrement(), stmt.getSyntheticChildNode("empty-increment")]) and
      node2.isBefore([stmt.getCondition(0), stmt.getSyntheticChildNode("empty-condition")])
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
      node1 = stmt.getSyntheticChildNode("loop-header") and // We don't model the exit condition, the loop header just has two outgoing edges
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
      node1.isAfter(binary.getRight()) and
      node2.isAfter(binary)
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
    exists(AugmentedAssignmentExpression assign |
      not exists(getShortCircuitingCondition(assign.getOperator()))
    |
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
      node1.isAfter([expr.getConsequence(), expr.getAlternative()]) and
      node2.isAfter(expr)
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
    exists(ParenthesizedExpression expr |
      node1.isAfter(expr.getChild()) and
      node2.isAfter(expr)
    )
  }

  predicate logicalValueStep(AstNode node1, AstNode node2) {
    exists(BinaryExpressionLike expr | expr.getOperator() = ["||", "??", "&&"] |
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
    or
    exists(SequenceExpression expr |
      node1 = max(int i | | expr.getChild(i) order by i) and
      node2 = expr
    )
  }
}

import MakeControlFlowGraph<ControlFlowGraphInput> as Cfg

private module Consistency {
  import Cfg::Debug
}
