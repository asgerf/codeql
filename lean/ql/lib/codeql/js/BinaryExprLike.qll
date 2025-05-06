private import javascript

/**
 * A binary expression, possibly one synthesized from a compound assignment operator.
 */
final class BinaryExpressionLike = BinaryExpressionLikeImpl;

abstract private class BinaryExpressionLikeImpl extends Node {
  abstract Node getLeft();

  abstract Node getRight();

  abstract string getOperator();
}

/**
 * A binary expression synthesized from a compound assignment operator.
 */
class BinaryExpressionInAssignment extends Node, BinaryExpressionLikeImpl {
  private AugmentedAssignmentExpression assignment;

  BinaryExpressionInAssignment() { this = getSyntheticNode(assignment, "binary-operator") }

  AugmentedAssignmentExpression getAssignment() { result = assignment }

  override Node getLeft() { result = assignment.getLeft() }

  override Node getRight() { result = assignment.getRight() }

  override string getOperator() { result + "=" = assignment.getOperator() }
}

private class BinaryExpressionAsLike extends BinaryExpressionLikeImpl instanceof BinaryExpression {
  override Node getLeft() { result = BinaryExpression.super.getLeft() }

  override Node getRight() { result = BinaryExpression.super.getRight() }

  override string getOperator() { result = BinaryExpression.super.getOperator() }
}
