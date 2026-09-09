private import unified
private import AllDataFlow

private predicate hasBothResultAndIncomingValue(Expr e) {
  e = any(CompoundAssignExpr a).getTarget()
}

private predicate hasResultValue(Expr e) {
  // For now, assume an expression has a result if it does not have an incoming value
  not e.hasIncomingValue()
  or
  hasBothResultAndIncomingValue(e)
}

private predicate hasOnlyIncomingValue(Expr e) {
  e.hasIncomingValue() and
  not hasBothResultAndIncomingValue(e)
}

private newtype TDataFlowNode =
  TValueNode(Expr expr) or
  TStrictlyIncomingValue(Expr expr) { hasBothResultAndIncomingValue(expr) }

/**
 * A node representing something that can have a value.
 */
class Node extends TDataFlowNode {
  /** Holds if this is the result of evaluating `expr`. */
  predicate isResultValue(Expr expr) { hasResultValue(expr) and this = TValueNode(expr) }

  /** Holds if this represents the value about to be assigned to `expr` or pattern-matched against `expr`. */
  predicate isIncomingValue(Expr expr) {
    hasOnlyIncomingValue(expr) and this = TValueNode(expr)
    or
    hasBothResultAndIncomingValue(expr) and this = TStrictlyIncomingValue(expr)
  }

  /** Gets the expression represented by this node. */
  Expr asExpr() { this = TValueNode(result) }

  /**
   * Gets the AST node wrapped by this data flow, if any.
   */
  AstNode getWrappedAstNode() { result = this.asExpr() or this = TStrictlyIncomingValue(result) }

  /** Get a string representation of this element. */
  string toString() {
    result = this.asExpr().toString()
    or
    exists(Expr expr |
      this = TStrictlyIncomingValue(expr) and
      result = "[incoming] " + expr.toString()
    )
  }

  /** Gets the location of this data flow node. */
  Location getLocation() { result = this.getWrappedAstNode().getLocation() }

  /** Gets the callable containing this data flow node. */
  Callable getEnclosingCallable() { result = this.getWrappedAstNode().getEnclosingCallable() }
}
