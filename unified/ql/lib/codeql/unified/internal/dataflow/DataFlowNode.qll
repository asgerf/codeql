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

private predicate hasPostUpdate(Expr expr) {
  exists(MemberAccessExpr member |
    (member.hasIncomingValue() or hasPostUpdate(member)) and
    expr = member.getBase()
  )
}

private newtype TDataFlowNode =
  TValueNode(Expr expr) or
  TStrictlyIncomingValue(Expr expr) { hasBothResultAndIncomingValue(expr) } or
  TPostUpdateNode(Expr expr) { hasPostUpdate(expr) } or
  TLocalVariableNode(LocalVariable v)

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

  /** Holds if this represents the value stored in the given local variable. */
  predicate isLocalVariable(LocalVariable v) { this = TLocalVariableNode(v) }

  /** Holds if this represents the updated state of the value returned by `expr` after it has been mutated by the surrounding assignment or call. */
  predicate isPostUpdate(Expr expr) { this = TPostUpdateNode(expr) }

  /** Gets the expression represented by this node. */
  Expr asExpr() { this = TValueNode(result) }

  /**
   * Gets the AST node wrapped by this data flow, if any.
   */
  AstNode getWrappedAstNode() {
    result = this.asExpr() or
    this = TStrictlyIncomingValue(result) or
    this = TPostUpdateNode(result)
  }

  /** Get a string representation of this element. */
  string toString() {
    result = this.asExpr().toString()
    or
    exists(Expr expr |
      this = TStrictlyIncomingValue(expr) and
      result = "[incoming] " + expr.toString()
      or
      this = TPostUpdateNode(expr) and
      result = "[post] " + expr.toString()
    )
    or
    exists(LocalVariable v |
      this.isLocalVariable(v) and
      result = "[variable] " + v.toString()
    )
  }

  /** Gets the location of this data flow node. */
  Location getLocation() {
    result = this.getWrappedAstNode().getLocation()
    or
    exists(LocalVariable v | this.isLocalVariable(v) and result = v.getLocation())
  }

  /** Gets the callable containing this data flow node. */
  Callable getEnclosingCallable() {
    result = this.getWrappedAstNode().getEnclosingCallable()
    or
    exists(LocalVariable v |
      this.isLocalVariable(v) and
      result = v.getABinding().getEnclosingCallable()
    )
  }
}

Node getPostUpdateNode(Node pre) {
  exists(Expr expr |
    pre.isResultValue(expr) and
    result.isPostUpdate(expr)
  )
}
