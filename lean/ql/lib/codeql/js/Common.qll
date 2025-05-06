private import javascript

string getStringValueFromNode(Node node) { result = node.(StringFragment).getValue() or none() }

int getIntValueFromNode(Node node) { result = node.(Number).getValue().toInt() or none() }

ContentSet getContentSetFromKey(Node key) {
  result.asPropertyName() = key.(PropertyIdentifier).getValue() or
  result.asPropertyName() = getStringValueFromNode(key) or
  result = ContentSet::arrayElementKnown(getIntValueFromNode(key))
}

Node getSyntheticNode(AstNode base, string name) { js_synthetic_node_def(result, base, name) }

Node getPostUpdate(Node node) { result = node } // TODO

/**
 * Gets the node acting as a junction for values being assigned to the given `node`, which appears in left-hand position of some form of assignment or in a parameter position.
 *
 * The L-value node decouples two orthogonal concerns:
 * - When handling an assignment-like operator, the assigned value should be made to flow into the L-value node, without regard to what kind of L-value it is.
 * - When handling a form of left-hand value, the L-value node should be taken as the "incoming" value, without regard to what context the left-hand value appears in.
 *
 * This helps avoids an N^2 case explosion that would typically arise if these concerns are not properly decoupled.
 */
Node getLValueNode(AstNode node) {
  isInPureLValuePosition(node) and result = node
  or
  isInImpureLValuePosition(node) and result = getSyntheticNode(node, "lvalue")
}

class SyntheticLValueNode extends Node, @js_synthetic_node {
  private Node lvalue;

  SyntheticLValueNode() { this = getSyntheticNode(lvalue, "value") }

  Node getOriginalNode() { result = lvalue }

  override string getAPrimaryQlClass() { result = "SyntheticLValueNode" }
}

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

predicate isLikelyArrayAccess(SubscriptExpression e) {
  none() // TODO
}
