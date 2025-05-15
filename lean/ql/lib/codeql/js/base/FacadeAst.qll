module JS {
  private import GeneratedAst::JS as G
  // This module re-exports the generated AST, shadowing the classes we have a facade for.
  // The generated AST refers to this module when referencing a type name, so predicates
  // have a more useful return type.
  import G

  /**
   * A compound assignment such as `x += e`.
   */
  class AugmentedAssignmentExpression extends G::AugmentedAssignmentExpression {
    /**
     * Gets a synthetic `binary-operator` node that represents the binary expression in the augmented assignment.
     */
    SyntheticNode getBinaryOperatorNode() { result = this.getSyntheticChildNode("binary-operator") }
  }

  /**
   * A `for (... in ...)` or `for (... of ...)` statement.
   */
  class ForInStatement extends G::ForInStatement {
    /**
     * Gets a synthetic `loop-header` node that represents the condition within the for-in loop.
     */
    SyntheticNode getLoopHeader() { result = this.getSyntheticChildNode("loop-header") }
  }

  final private class FinalForStatement = G::ForStatement;

  /**
   * A `for` statement.
   */
  class ForStatement extends FinalForStatement {
    /** Gets the loop condition or a synthetic `empty-condition` node if the condition was omitted. */
    AstNode getConditionOrEmptyNode() {
      result = super.getCondition(0)
      or
      result = this.getSyntheticChildNode("empty-condition")
    }

    /** Gets the increment expression or a synthetic `empty-increment` node if the increment was omitted. */
    AstNode getIncrementOrEmptyNode() {
      result = super.getIncrement()
      or
      result = this.getSyntheticChildNode("empty-increment")
    }
  }
}
