private import codeql.js.base.BaseLayer

module LeftHandValues {
  /**
   * Holds if `node` appears in a position where it is written to and not read from.
   *
   * For example, this holds for the target of an assignment (`x = e`) but not for a compound assignment (`x += e`)
   * which is considered an impure l-value position.
   */
  predicate isInPureLValuePosition(AstNode node) {
    node = any(AssignmentExpression e).getLeft()
    or
    node = any(VariableDeclarator v).getName()
    or
    node = any(ForInStatement e).getLeft()
    or
    node = any(PairPattern p).getValue()
    or
    node = any(ArrayPattern p).getChild(_) and not node instanceof RestPattern
    or
    node = any(RestPattern p).getChild()
    // TODO: parentheses
  }

  /**
   * Holds if `node` appears in a position where it is both read from and written to.
   *
   * Concretely, this holds for the target of a compound assignment (`x += e`) or update expression (`x++`).
   */
  predicate isInImpureLValuePosition(AstNode node) {
    node = any(AugmentedAssignmentExpression e).getLeft()
    or
    node = any(UpdateExpression e).getArgument()
    // TODO: parentheses
  }

  predicate isInLValuePosition(AstNode node) {
    isInPureLValuePosition(node)
    or
    isInImpureLValuePosition(node)
  }
}
