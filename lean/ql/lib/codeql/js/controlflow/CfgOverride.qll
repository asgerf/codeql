private import javascript
private import codeql.js.controlflow.ValueFilter

private class CfgNode extends AstNode {
  predicate isBefore(AstNode node) { this = node.getSyntheticChildNode("cfg-begin") }

  predicate isAfter(AstNode node) { this = node.getSyntheticChildNode("cfg-end") }

  predicate isLValue(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue-begin") }

  predicate isLValueEnd(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue-end") }
}

private class CfgCondition extends AstNode {
  predicate isValueOf(AstNode node) { this = node.getSyntheticChildNode("cfg-end") }

  predicate isLValue(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue-begin") }
}

abstract private class CfgOverride extends AstNode {
  /**
   * Induces a CFG edge from the end of `node1` to the beginning of `node2`.
   *
   * If the value of `node1`/`node2` is either `this.begin()`, `this.end()`, or is any synthetic node,
   * the value is taken as-is, and won't be mapped to another begin/end node.
   */
  abstract predicate succ(CfgNode child1, CfgNode child2);

  /**
   * Holds if `condition` evaluating to `f` causes `thenCase` to be executed, and `elseCase` otherwise.
   */
  predicate conditionalSucc(
    CfgCondition condition, ValueFilter f, CfgNode thenCase, CfgNode elseCase
  ) {
    none()
  }

  /**
   * Holds if exceptions thrown in `scope` should be handled by `handler`.
   */
  predicate exceptionHandler(Node scope, Node handler) { none() }

  final SyntheticNode begin() { result = this.getSyntheticChildNode("cfg-begin") }

  final Node end() { result = this }
}

/**
 * Overrides the CFG for the synthetic L-value nodes generated for a node in lvalue position.
 *
 * For example, for an assignment `x.f += 1`, the CFG for the regular AST nodes in `x.f` will contain
 * the initial read of `x.f`. The CFG for the synthetic L-value node will contain the store.
 *
 * If this class is not implemented for a particular L-value node, the L-value nodes will be arranged in a pre-order left-to-right CFG.
 */
abstract private class LValueCfgOverride extends AstNode {
  LValueCfgOverride() { LeftHandValues::isInLValuePosition(this) }

  /**
   * Induces a CFG edge from the end of the L-value node of `node1` to the beginning of the L-value node of `node2`.
   *
   * If the value of `node1`/`node2` is either `this.begin()`, `this.end()`, or is any synthetic node,
   * the value is taken as-is, and won't be mapped to another begin/end node.
   */
  abstract predicate succ(CfgCondition child1, CfgCondition child2);

  /**
   * Holds if `condition` evaluating to `f` causes `thenCase` to be executed, and `elseCase` otherwise.
   */
  predicate conditionalSucc(
    CfgCondition condition, ValueFilter f, CfgCondition thenCase, CfgCondition elseCase
  ) {
    none()
  }

  final SyntheticNode begin() { result = this.getSyntheticChildNode("lvalue-begin") }

  final Node end() { result = this.getSyntheticChildNode("lvalue-end") }
}

predicate shouldSynthetizeCfgNode(AstNode node, string tag) {
  node instanceof CfgOverride and tag = ["cfg-begin"]
  or
  LeftHandValues::isInLValuePosition(node) and tag = ["lvalue-begin", "lvalue-end"]
}

/**
 * Gets the CFG node and data flow node at the beginning of assignment into the given lvalue.
 *
 * As a data flow node, this node holds the "incoming" values being assigned into the lvalue.
 */
Node getLValueBegin(Node lvalue) { result = lvalue.getSyntheticChildNode("lvalue-begin") }

/**
 * Gets the CFG node at the end of assignment to the given lvalue.
 */
Node getLValueEnd(Node lvalue) { result = lvalue.getSyntheticChildNode("lvalue-end") }

class ForStatementCfg extends CfgOverride, ForStatement {
  override predicate succ(CfgNode node1, CfgNode node2) {
    node1.isBefore(this) and node2.isBefore(this.getInitializer())
    or
    node1.isAfter(this.getInitializer()) and node2.isBefore(this.getCondition(0))
    or
    node1.isAfter(this.getCondition(0)) and node2.isBefore(this.getIncrement())
    or
    node1.isAfter(this.getIncrement()) and node2.isBefore(this.getCondition(0))
  }

  override predicate conditionalSucc(
    CfgCondition condition, ValueFilter f, CfgNode thenCase, CfgNode elseCase
  ) {
    condition.isValueOf(this.getCondition(0)) and
    f = ValueFilter::TTruthy() and
    thenCase.isBefore(this.getBody()) and
    elseCase.isAfter(this)
  }
}

class ForInStatementCfg extends CfgOverride, ForInStatement {
  private SyntheticNode getLoopHeader() { result = this.getSyntheticChildNode("loop-header") }

  override predicate succ(CfgNode node1, CfgNode node2) {
    node1 = this.begin() and node2 = this.getRight()
    or
    node1 = this.getRight() and node2 = this.getLoopHeader()
    or
    node1 = this.getLoopHeader() and node2 = this.getLeft()
    or
    node1 = this.getLeft() and node2 = getLValueBegin(this.getLeft())
    or
    node1 = getLValueEnd(this.getLeft()) and node2 = this.getBody()
    or
    node1 = this.getBody() and node2 = this.getLoopHeader()
  }

  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = this.getLoopHeader() and
    f = ValueFilter::TTruthy() and
    thenCase = this.getBody() and
    elseCase = this.end()
  }
}

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

class LazyBinaryExpression extends CfgOverride, BinaryExpression {
  LazyBinaryExpression() { this.getOperator() = ["&&", "||", "??"] }

  override predicate succ(CfgNode node1, CfgNode node2) {
    node1 = this.begin() and node2 = this.getLeft()
    or
    node1 = this.getRight() and node2 = this.end()
  }

  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = this.getLeft() and
    f = getShortCircuitingFilter(this.getOperator()) and
    thenCase = this.end() and
    elseCase = this.getRight()
  }
}

class LazyAugmentedAssignment extends CfgOverride, AugmentedAssignmentExpression {
  LazyAugmentedAssignment() { this.getOperator() = ["&&=", "||=", "??="] }

  private BinaryExpressionInAssignment getBinaryExprNode() { result.getAssignment() = this }

  override predicate succ(CfgNode node1, CfgNode node2) {
    node1 = this.begin() and node2 = this.getLeft()
    or
    node1 = this.getRight() and node2 = this.getBinaryExprNode()
    or
    node1 = this.getBinaryExprNode() and node2 = this.end()
  }

  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = this.getLeft() and
    f = getShortCircuitingFilter(this.getBinaryExprNode().getOperator()) and
    thenCase = this.end() and // short-circuit the whole assignment, not just the binary operator
    elseCase = this.getRight()
  }
}

class AssignmentPatternCfg extends LValueCfgOverride, AssignmentPattern {
  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = this.begin() and
    f = ValueFilter::TNotNullLike() and
    thenCase = this.getLeft() and
    elseCase = this.getRight()
  }

  override predicate succ(CfgNode node1, CfgNode node2) {
    node1 = this.getRight() and node2 = this.getLeft()
    or
    node1 = this.getLeft() and node2 = this.end()
  }
}

class OptionalChainAccessorCfg extends CfgOverride, OptionalChaining::OptionalChainInnerAccessor {
  override predicate succ(CfgNode node1, CfgNode node2) {
    node1 = this.begin() and node2 = this.getRoot()
    or
    // The next expression to evaluate depends on the type of node
    exists(MemberExpression expr | this = expr |
      node1 = this.getTrueOutcomeForRootExpr() and node2 = this.end()
    )
    or
    exists(SubscriptExpression expr | this = expr |
      node1 = this.getTrueOutcomeForRootExpr() and node2 = expr.getIndex()
      or
      node1 = expr.getIndex() and node2 = this.end()
    )
    or
    exists(CallExpression call | this = call |
      node1 = this.getTrueOutcomeForRootExpr() and node2 = call.getArguments()
      or
      node1 = call.getArguments() and node2 = this.end()
    )
  }

  override predicate conditionalSucc(Node condition, ValueFilter f, Node thenCase, Node elseCase) {
    condition = this.getRoot() and
    f = ValueFilter::TNotNullLike() and
    thenCase = this.getTrueOutcomeForRootExpr() and
    elseCase = this.getOutermostAccessor().getFalseOutcome()
  }
}
