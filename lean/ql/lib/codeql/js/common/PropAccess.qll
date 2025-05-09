private import CommonLayer

/**
 * An expression that accesses a property, either via a dot expression (`foo.bar`) or subscript (`foo[bar]`).
 *
 * Note that destructuring patterns are not coverered by this class.
 */
final class PropAccess = PropAccessImpl;

abstract private class PropAccessImpl extends Expression {
  abstract AstNode getObject();

  abstract AstNode getPropertyNameNode();

  /** Holds if this is an expression of form `foo?.bar` or `foo?.[bar]`. */
  predicate isOptionalChain() { this instanceof OptionalChaining::OptionalChainInnerAccessor }
}

private class MemberExpressionAsPropAccess extends PropAccessImpl instanceof MemberExpression {
  override AstNode getObject() { result = MemberExpression.super.getObject() }

  override AstNode getPropertyNameNode() { result = MemberExpression.super.getProperty() }
}

private class SubscriptExpressionAsPropAccess extends PropAccessImpl instanceof SubscriptExpression {
  override AstNode getObject() { result = SubscriptExpression.super.getObject() }

  override AstNode getPropertyNameNode() { result = SubscriptExpression.super.getIndex() }
}
