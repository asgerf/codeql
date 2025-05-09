private import codeql.js.base.BaseLayer

module OptionalChaining {
  /**
   * Gets the `root` in `root?.x`, `root?.[x]`, or `root?.()`.
   */
  AstNode getImmediateOptionalChainRoot(AstNode node) {
    // `object?.x`
    exists(MemberExpression member |
      node = member and
      exists(member.getOptionalChain()) and
      result = member.getObject()
    )
    or
    // `object?.[x]`
    exists(SubscriptExpression member |
      node = member and
      exists(member.getOptionalChain()) and
      result = member.getObject()
    )
    or
    // `fun?.()`
    exists(CallExpression call |
      node = call and
      exists(call.getOptionalChain()) and
      result = call.getFunction()
    )
  }

  /**
   * Gets the rooot of the optional chain for `node`, such as `root` in `root?.x.y.foo()`.
   */
  AstNode getOptionalChainRoot(AstNode node) {
    result = getImmediateOptionalChainRoot(node)
    or
    not exists(getImmediateOptionalChainRoot(node)) and
    result = getOptionalChainRoot(getChainBase(node))
  }

  /**
   * Get the base of `expr` if `expr` is a type of expression that can be part of an optional chain.
   */
  Expression getChainBase(Expression expr) {
    result = expr.(MemberExpression).getObject()
    or
    result = expr.(SubscriptExpression).getObject()
    or
    result = expr.(CallExpression).getFunction()
  }

  /**
   * The innermost accessor in an optional chain, such as the `x?.y` in `x?.y.z.w`.
   */
  class OptionalChainInnerAccessor extends Expression {
    private AstNode root;

    OptionalChainInnerAccessor() { root = getImmediateOptionalChainRoot(this) }

    /** Gets the `x` in `x?.y.z.w` */
    AstNode getRoot() { result = root }

    /** Gets a synthetic node representing the value of the root expression if it was a non-null value. */
    SyntheticNode getTrueOutcomeForRootExpr() {
      result = this.getRoot().getSyntheticChildNode("true-outcome")
    }
  }

  /**
   * The outermost accessor in an optional chain, such as `x?.y.z.w`.
   *
   * The intermediate expressions in a long chain are not instances of this class.
   */
  class OptionalChainOuterAccessor extends Expression {
    private AstNode root;

    OptionalChainOuterAccessor() {
      root = getOptionalChainRoot(this) and
      not this = getChainBase(_)
    }

    /** Gets the `x` in `x?.y.z.w` */
    AstNode getRoot() { result = root }

    /** Gets the `x?.y` in `x?.y.z.w` */
    OptionalChainInnerAccessor getInnermostAccessor() { result.getRoot() = root }

    /** Gets a synthetic node representing the value of the root expression if it was a non-null value. */
    SyntheticNode getTrueOutcomeForRootExpr() {
      result = this.getRoot().getSyntheticChildNode("true-outcome")
    }
  }
}
