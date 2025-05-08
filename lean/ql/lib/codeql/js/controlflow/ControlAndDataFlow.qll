private import javascript

module ValueFilter {
  newtype TValueFilter =
    TTruthy() or
    TFalsy() or
    TNullLike() or
    TNotNullLike()

  class ValueFilter extends TValueFilter {
    string toString() {
      this = TTruthy() and result = "truthy"
      or
      this = TFalsy() and result = "falsy"
      or
      this = TNullLike() and result = "null-like"
      or
      this = TNotNullLike() and result = "not-null-like"
    }

    private ValueFilter intersect1(ValueFilter other) {
      this = TTruthy() and other = TNotNullLike() and result = TTruthy()
      or
      this = TFalsy() and other = TNullLike() and result = TNullLike()
    }

    /**
     * Gets the filter representing the intersection of `this` and `other`.
     *
     * Has no result if no values can satisfy both filters.
     */
    ValueFilter intersect(ValueFilter other) {
      this = other and result = this
      or
      result = this.intersect1(other)
      or
      result = other.intersect1(this)
    }

    ValueFilter negate() {
      this = TTruthy() and result = TFalsy()
      or
      this = TFalsy() and result = TTruthy()
      or
      this = TNullLike() and result = TNotNullLike()
      or
      this = TNotNullLike() and result = TNullLike()
    }
  }
}

class ValueFilter = ValueFilter::ValueFilter;

/**
 * Gets the filter matching the set of values that cause the given logical operator to short-circuit.
 */
private ValueFilter getShortCircuitingFilter(string operator) {
  result = ValueFilter::TTruthy() and operator = "||"
  or
  result = ValueFilter::TFalsy() and operator = "&&"
  or
  result = ValueFilter::TNotNullLike() and operator = "??"
}

/** Gets the filter corresponding to the "then" outcome of `node` in cases where it is not the "truthy" filter. */
private ValueFilter getSpecialThenFilter(AstNode node) {
  node = any(BinaryExpressionLike bin | bin.getOperator() = "??").getLeft() and
  result = ValueFilter::TNotNullLike()
  or
  node instanceof AssignmentPattern and
  result = ValueFilter::TNotNullLike()
}

private ValueFilter getThenFilter(AstNode node) {
  result = getSpecialThenFilter(node)
  or
  Conditions::isCondition(node) and
  not exists(getSpecialThenFilter(node)) and
  result = ValueFilter::TTruthy()
}

/**
 * Holds if `node1 -> node2` is both a control flow and data flow edge, that is taken
 * when `node1` has a value that satisfies `filter`.
 */
predicate conditionalControlAndDataFlow(Node node1, Node node2, ValueFilter filter) {
  exists(ValueFilter thenFilter | thenFilter = getThenFilter(node1) |
    node2 = Conditions::getThenOutcome(node1) and
    filter = thenFilter
    or
    node2 = Conditions::getElseOutcome(node1) and
    filter = thenFilter.negate()
  )
}

predicate controlAndDataFlow(Node node1, Node node2) {
  exists(LogicalNot expr |
    node1 = Conditions::getThenOutcome(expr.getArgument()) and
    node2 = Conditions::getElseOutcome(expr)
    or
    node1 = Conditions::getElseOutcome(expr.getArgument()) and
    node2 = Conditions::getThenOutcome(expr)
  )
  or
  exists(BinaryExpressionLike expr |
    expr.getOperator() = "&&" and
    node1 = Conditions::getThenOutcome(node1) and
    node2 = expr.getRight()
    or
    expr.getOperator() = ["||", "??", "&&"] and
    node1 = expr.getRight() and
    node2 = expr
  )
  or
  exists(AssignmentPattern pattern |
    node1 = pattern.getRight() and
    node2 = getLValueNode(pattern.getLeft())
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
/*
 *  exists(BinaryExpressionLike expr | node1 = expr.getLeft() |
 *    filter = getShortCircuitingFilter(expr.getOperator()) and
 *    (
 *      // For short-circuiting assignments, the whole assignment is skipped
 *      if expr instanceof BinaryExpressionInAssignment
 *      then node2 = expr.(BinaryExpressionInAssignment).getAssignment()
 *      else node2 = expr
 *    )
 *    or
 *    filter = getShortCircuitingFilter(expr.getOperator()).negate() and
 *    node2 = expr.getRight().getSyntheticChildNode("branch-target")
 *  )
 *  or
 *  exists(AssignmentPattern pattern |
 *    // Example:
 *    //
 *    //   let {x: y = 3} = z
 *    //
 *    // This is equivalent to:
 *    //
 *    //   let y = z.x ?? 3
 *    //
 *    // We generate the same steps as for the '??' operator
 *    node1 = getLValueNode(pattern)
 *  |
 *    node2 = getLValueNode(pattern.getLeft()) and
 *    filter = ValueFilter::TNotNullLike()
 *    or
 *    node2 = pattern.getRight().getSyntheticChildNode("branch-target") and
 *    filter = ValueFilter::TNullLike()
 *  )
 */
