private import javascript

/**
 * An expression that accesses a property, either via a dot expression (`foo.bar`) or subscript (`foo[bar]`).
 *
 * Note that destructuring patterns are not coverered by this class.
 */
final class PropAccess = PropAccessImpl;

abstract private class PropAccessImpl extends Expression {
  abstract Node getObject();

  abstract Node getPropertyNameNode();
}

private class MemberExpressionAsPropAccess extends PropAccessImpl instanceof MemberExpression {
  override Node getObject() { result = MemberExpression.super.getObject() }

  override Node getPropertyNameNode() { result = MemberExpression.super.getProperty() }
}

private class SubscriptExpressionAsPropAccess extends PropAccessImpl instanceof SubscriptExpression {
  override Node getObject() { result = SubscriptExpression.super.getObject() }

  override Node getPropertyNameNode() { result = SubscriptExpression.super.getIndex() }
}
