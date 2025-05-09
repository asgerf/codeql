private import javascript
private import codeql.js.controlflow.ControlFlowShared
private import ValueFilter

module ControlFlowConfig implements ControlFlowSig {
  class CfgScope = FunctionOrProgram;

  predicate getCfgScope = getEnclosingFunctionOrProgram/1;

  predicate needsCfg(Node node) {
    node instanceof Statement
    or
    node instanceof Expression
    or
    node instanceof Program
  }
}

module BaselineCfg = ControlFlowShared<ExecutionOrder, ControlFlowConfig>;

private import ExecutionOrder
private import BaselineCfg

/**
 * Gets the filter matching the set of values that cause the given logical operator to short-circuit.
 */
private ValueFilter getShortCircuitingFilter(string operator) {
  operator = "||" and result = ValueFilter::TTruthy()
  or
  operator = "&&" and result = ValueFilter::TFalsy()
  or
  operator = "??" and result = ValueFilter::TNotNullLike()
}

abstract class CfgNodeBase extends AstNode {
  predicate succ(Node child1, Node child2) { none() }

  /**
   * Holds if `condition` evaluating to `f` causes `thenCase` to be executed, and `elseCase` otherwise.
   */
  predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) { none() }

  predicate exceptionHandler(Node scope, Node handler) { none() }
}

class ForStatementCfg extends CfgNodeBase, ForStatement {
  override predicate succ(Node node1, Node node2) {
    node1 = this and node2 = this.getInitializer()
    or
    node1 = this.getInitializer() and node2 = this.getCondition(0)
    or
    node1 = this.getCondition(0) and node2 = this.getBody()
    or
    node1 = this.getBody() and node2 = this.getIncrement()
    or
    node1 = this.getIncrement() and node2 = this.getCondition(0)
  }

  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = this.getCondition(0) and
    f = ValueFilter::TTruthy() and
    thenCase = this.getBody() and
    elseCase = this
  }
}

class BinaryExpressionLikeCfg extends CfgNodeBase instanceof BinaryExpressionLike {
  override predicate succ(Node node1, Node node2) { node1 = this and node2 = super.getLeft() }

  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = super.getLeft() and
    f = getShortCircuitingFilter(super.getOperator()) and
    (
      // For compound assignment operators, the entire assignment is short-circuited
      if this instanceof BinaryExpressionInAssignment
      then thenCase = this.(BinaryExpressionInAssignment).getAssignment()
      else thenCase = this
    ) and
    elseCase = super.getRight()
  }
}

/**
 * Holds if `condition` satisfying `filter` immediately causes control to evaluate `thenCase`, and `elseCase` otherwise,
 * and after the `thenCase`/`elseCase` completes, control reaches `exit`.
 *
 * As a special case, if `thenCase` or `elseCase` equals `exit` it means that the given branch will cause `exit`
 * to immediately complete with the same value as `condition`. This can be used to handle short-circuiting operators
 * and if-statements with omitted `else`.
 *
 * The `thenCase` and `elseCase` should either refer to `exit` or a node that satisfies `ExecutionOrder::isExecutedOutOfOrder`.
 */
predicate branchAndJoinFlow(
  Node condition, ValueFilter filter, Node thenCase, Node elseCase, Node exit
) {
  exists(IfStatement stmt |
    condition = stmt.getCondition() and
    filter = ValueFilter::TTruthy() and
    thenCase = stmt.getConsequence() and
    (
      elseCase = stmt.getAlternative().getChild() // note: getAlternative() does not return a Statement (TODO: clean up in tree-sitter grammar)
      or
      not exists(stmt.getAlternative()) and
      elseCase = stmt
    ) and
    exit = stmt
  )
  or
  exists(BinaryExpressionLike binary |
    condition = binary.getLeft() and
    filter = getShortCircuitingFilter(binary.getOperator()) and
    (
      // For compound assignment operators, the entire assignment is short-circuited
      if binary instanceof BinaryExpressionInAssignment
      then thenCase = binary.(BinaryExpressionInAssignment).getAssignment() // FIXME: does not equal 'exit' so it will step to the beginning of the assignment
      else thenCase = binary
    ) and
    elseCase = binary.getRight() and
    exit = binary
  )
  or
  exists(TernaryExpression expr |
    condition = expr.getCondition() and
    filter = ValueFilter::TTruthy() and
    thenCase = expr.getConsequence() and
    elseCase = expr.getAlternative() and
    exit = expr
  )
}

private import OptionalChaining

/**
 * Holds if `condition` satisfying `filter` immediately causes control to start evaluating `thenCase`, and `elseCase` otherwise.
 *
 * As a special case, if `thenCase` or `elseCase` equals `exit` it means that the given branch will cause `exit`
 * to complete immediately with the same value as `condition`.
 *
 * This is similar to `branchAndJoinFlow` except it does not add flow from `thenCase`/`elseCase` to `exit` (i.e. no join).
 */
predicate branchFlow(Node condition, ValueFilter filter, Node thenCase, Node elseCase, Node exit) {
  exists(WhileStatement stmt |
    condition = stmt.getCondition() and
    filter = ValueFilter::TTruthy() and
    thenCase = stmt.getBody() and
    elseCase = stmt and
    exit = stmt
  )
  or
  exists(DoStatement stmt |
    condition = stmt.getCondition() and
    filter = ValueFilter::TTruthy() and
    thenCase = stmt.getBody() and
    elseCase = stmt and
    exit = stmt
  )
  or
  exists(ForStatement stmt |
    condition = stmt.getCondition(0) and
    filter = ValueFilter::TTruthy() and
    thenCase = stmt.getBody() and
    elseCase = stmt and
    exit = stmt
  )
  or
  exists(OptionalChainOuterAccessor expr |
    condition = expr.getRoot() and
    filter = ValueFilter::TNotNullLike() and
    thenCase = expr.getTrueOutcomeForRootExpr() and
    elseCase = expr and
    exit = expr
  )
}

bindingset[node, exit]
private Node getAsTargetNode(Node node, Node exit) {
  if node = exit
  then result = exit
  else (
    result = getSyntheticBeginNode(node)
    or
    node instanceof SyntheticNode and
    result = node
  )
}

predicate conditionalControlAndDataFlowEdge(Node node1, Node node2, ValueFilter filter) {
  exists(Node condition, ValueFilter conditionFilter, Node thenCase, Node elseCase, Node exit |
    branchAndJoinFlow(condition, conditionFilter, thenCase, elseCase, exit)
    or
    branchFlow(condition, filter, thenCase, elseCase, exit)
  |
    node1 = condition and
    filter = conditionFilter and
    node2 = getAsTargetNode(thenCase, exit)
    or
    node1 = condition and
    filter = conditionFilter.negate() and
    node2 = getAsTargetNode(elseCase, exit)
  )
}

predicate unconditionalControlAndDataFlowEdge(Node node1, Node node2) {
  exists(Node condition, ValueFilter conditionFilter, Node thenCase, Node elseCase, Node exit |
    branchAndJoinFlow(condition, conditionFilter, thenCase, elseCase, exit)
  |
    node1 = BaselineCfg::getEnd(thenCase) and
    node2 = exit
    or
    node1 = BaselineCfg::getEnd(elseCase) and
    node2 = exit
  )
}

predicate step(Node node1, Node node2) {
  exists(WhileStatement stmt |
    node1 = getDetachedPredecessor(stmt.getCondition()) and
    node2 = getSyntheticBeginNode(stmt.getCondition())
    or
    node1 = getSyntheticEndNode(stmt.getBody()) and
    node2 = getSyntheticBeginNode(stmt.getCondition())
  )
  or
  exists(DoStatement stmt |
    node1 = getDetachedPredecessor(stmt.getBody()) and
    node2 = getSyntheticBeginNode(stmt.getBody())
    or
    node1 = getSyntheticEndNode(stmt.getBody()) and
    node2 = getSyntheticBeginNode(stmt.getCondition())
  )
  or
  exists(ForStatement stmt |
    exists(int i |
      node1 = getDetachedPredecessor(stmt.getCondition(i)) and
      node2 = getSyntheticBeginNode(stmt.getCondition(i))
    )
    or
    node1 = getSyntheticEndNode(stmt.getBody()) and
    node2 = getSyntheticBeginNode(stmt.getIncrement())
    or
    node1 = getSyntheticEndNode(stmt.getIncrement()) and
    node2 = getSyntheticBeginNode(stmt.getCondition(0))
  )
  or
  exists(ForInStatement stmt |
    node1 = getDetachedPredecessor(stmt) and
    node2 = getSyntheticBeginNode(stmt.getRight())
    or
    node1 = getSyntheticEndNode(stmt.getRight()) and
    node2 = stmt.getSyntheticChildNode("loop-header")
    or
    node1 = stmt.getSyntheticChildNode("loop-header") and
    node2 = getLValueNode(stmt.getLeft())
    or
    // or
    // node1 = getAfterLValueNode(stmt.getLeft()) and // TODO!
    // node2 = getSyntheticBeginNode(stmt.getBody())
    node1 = getSyntheticEndNode(stmt.getBody()) and
    node2 = stmt.getSyntheticChildNode("loop-header")
  )
  or
  exists(OptionalChainInnerAccessor chain |
    node1 = getDetachedPredecessor(chain.getRoot()) and
    node2 = getSyntheticBeginNode(chain.getRoot())
    or
    node1 = chain.getTrueOutcomeForRootExpr() and
    node2 = getDetachedSuccessor(chain.getRoot())
  )
}
