private import codeql.js.common.All
private import codeql.js.controlflow.ValueFilter
private import codeql.shared.LanguageCfg::ControlFlow<Location, LanguageBase, LanguageCommon>
// TODO: pass in ValueFilter in isCondition?
private import codeql.js.controlflow.ValueFilter::ValueFilter

/**
 * An explicit step from `node1` to `node2`.
 *
 * The existence of an explicit step `node1 -> node2` suppresses the default left-to-right edge out of `node1` and
 * as well as the default left-to-right edge into `node2`.
 */
pragma[nomagic]
predicate explicitStep(CfgNode node1, CfgNode node2) {
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
    node2 = stmt.getSyntheticChildNode("loop-header")
    or
    node1 = stmt.getSyntheticChildNode("loop-header") and
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
  or
  exists(LogicalNot expr |
    node1.isAfterTrue(expr.getArgument()) and
    node2.isAfterFalse(expr)
    or
    node1.isAfterFalse(expr.getArgument()) and
    node2.isAfterTrue(expr)
  )
}

private import MakeCfg<explicitStep/2> as Cfg
import Cfg

predicate step = Cfg::step/2;
