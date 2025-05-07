private import codeql.js.base.BaseLayer

class OptionalChainExpression = OptionalChaining::OptionalChainExpression;

module OptionalChaining {
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

  AstNode getOptionalChainRoot(AstNode node) {
    result = getImmediateOptionalChainRoot(node)
    or
    not exists(getImmediateOptionalChainRoot(node)) and
    result = getOptionalChainRoot(getChainBase(node))
  }

  Expression getChainBase(Expression expr) {
    result = expr.(MemberExpression).getObject()
    or
    result = expr.(SubscriptExpression).getObject()
    or
    result = expr.(CallExpression).getFunction()
  }

  /**
   * The outermost accessor in an optional chain, such as `x?.y.z.w`.
   *
   * The intermediate expressions in a long chain are not instances of this class.
   */
  class OptionalChainExpression extends Expression {
    private AstNode root;

    OptionalChainExpression() {
      root = getOptionalChainRoot(this) and
      not this = getChainBase(_)
    }

    /** Gets the `x` in `x?.y.z.w` */
    AstNode getRoot() { result = root }

    /** Gets the `x?.y` in `x?.y.z.w` */
    AstNode getFirstAccessor() { getChainBase(result) = root }
  }
}
