private import All

/**
 * An expression that may be part of an optional chain: member `e.f`, subscript `e[f]`, and calls `f()`.
 */
final class ChainableExpression = ChainableExpressionImpl;

abstract private class ChainableExpressionImpl extends Expression {
  abstract Expression getBase();

  abstract predicate isOptional();
}

private class ChainableMemberExpression extends ChainableExpressionImpl, MemberExpression {
  override Expression getBase() { result = this.getObject() }

  override predicate isOptional() { exists(this.getOptionalChain()) }
}

private class ChainableSubscriptExpression extends ChainableExpressionImpl, SubscriptExpression {
  override Expression getBase() { result = this.getObject() }

  override predicate isOptional() { exists(this.getOptionalChain()) }
}

private class ChainableCallExpression extends ChainableExpressionImpl, CallExpression {
  override Expression getBase() { result = this.getFunction() }

  override predicate isOptional() { exists(this.getOptionalChain()) }
}

/**
 * The innermost accessor in an optional chain expression, such as `x?.y`, `x?.[y]`, or `x?.()`.
 */
class OptionalChainExpression extends ChainableExpression {
  OptionalChainExpression() { this.isOptional() }

  private ChainableExpression getAnAccessorInChain() {
    result = this
    or
    result.getBase() = this.getAnAccessorInChain() and
    not result.isOptional()
  }

  /**
   * Gets the outermost accessor in an optional chain. For example, this could map from `x?.y` to `x?.y.z.w`.
   */
  ChainableExpression getOutermostAccessor() {
    result = this.getAnAccessorInChain() and
    not result = any(ChainableExpression e).getBase()
  }
}

final private class FinalMemberExpression = MemberExpression;

/** An expression of form `x?.y` */
class OptionalMemberExpression extends OptionalChainExpression, FinalMemberExpression { }

final private class FinalSubscriptExpression = SubscriptExpression;

/** An expression of form `x?.[y]` */
class OptionalSubscriptExpression extends OptionalChainExpression, FinalSubscriptExpression { }

final private class FinalCallExpression = CallExpression;

/** An expression of form `f?.()` */
class OptionalCallExpression extends OptionalChainExpression, FinalCallExpression { }
