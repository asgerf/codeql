private import codeql.js.base.GeneratedAst::JS

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
   * The root expression of an optional chain, such as the `x` in `x?.y.z.w`.
   */
  class OptionalChainRoot extends Expression {
    OptionalChainRoot() { this = getImmediateOptionalChainRoot(_) }

    OptionalChainInnerAccessor getInnermostAccessor() { this = result.getRoot() }

    OptionalChainOuterAccessor getOutermostAccessor() { this = result.getRoot() }

    /** Gets a synthetic node representing the value of the root expression if it was not null or undefined. */
    SyntheticNode getTrueOutcome() { result = this.getSyntheticChildNode("true-outcome") }

    /** Gets a synthetic node representing the value of the root expression if it was null or undefined. */
    SyntheticNode getFalseOutcome() { result = this.getSyntheticChildNode("false-outcome") }
  }

  /**
   * The innermost accessor in an optional chain, such as the `x?.y` in `x?.y.z.w`.
   */
  class OptionalChainInnerAccessor extends Expression {
    private AstNode root;

    OptionalChainInnerAccessor() { root = getImmediateOptionalChainRoot(this) }

    /** Gets the `x` in `x?.y.z.w` */
    AstNode getRoot() { result = root }

    OptionalChainOuterAccessor getOutermostAccessor() { result.getRoot() = root }
  }

  class OptionalMemberExpression extends OptionalChainInnerAccessor, MemberExpression { }

  class OptionalSubscriptExpression extends OptionalChainInnerAccessor, SubscriptExpression { }

  class OptionalCallExpression extends OptionalChainInnerAccessor, CallExpression { }

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
  }
}
