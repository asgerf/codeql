private import CommonLayer

/**
 * A binary expression, possibly one synthesized from a compound assignment operator.
 */
final class BinaryExpressionLike = BinaryExpressionLikeImpl;

abstract private class BinaryExpressionLikeImpl extends AstNode {
  abstract AstNode getLeft();

  abstract AstNode getRight();

  abstract string getOperator();
}

/**
 * A binary expression synthesized from a compound assignment operator.
 */
class BinaryExpressionInAssignment extends SyntheticNode, BinaryExpressionLikeImpl {
  private AugmentedAssignmentExpression assignment;

  BinaryExpressionInAssignment() { this = assignment.getSyntheticChildNode("binary-operator") }

  AugmentedAssignmentExpression getAssignment() { result = assignment }

  override AstNode getLeft() { result = assignment.getLeft() }

  override AstNode getRight() { result = assignment.getRight() }

  override string getOperator() { result + "=" = assignment.getOperator() }
}

private class BinaryExpressionAsLike extends BinaryExpressionLikeImpl instanceof BinaryExpression {
  override AstNode getLeft() { result = BinaryExpression.super.getLeft() }

  override AstNode getRight() { result = BinaryExpression.super.getRight() }

  override string getOperator() { result = BinaryExpression.super.getOperator() }
}
