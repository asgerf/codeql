private import javascript
private import LeftHandValues

string getStringValueFromNode(Node node) { result = node.(StringFragment).getValue() or none() }

int getIntValueFromNode(Node node) { result = node.(Number).getValue().toInt() or none() }

ContentSet getContentSetFromKey(Node key) {
  result.asPropertyName() = key.(PropertyIdentifier).getValue() or
  result.asPropertyName() = getStringValueFromNode(key) or
  result = ContentSet::arrayElementKnown(getIntValueFromNode(key))
}

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
  isInImpureLValuePosition(node) and result = node.getSyntheticChildNode("lvalue")
}

predicate isLikelyArrayAccess(SubscriptExpression e) {
  none() // TODO
}

string inferNameFromNode(Node node) {
  result = node.(Identifier).getValue()
  or
  result = node.(PropertyIdentifier).getValue()
  or
  result = node.(PropAccess).getPropertyNameNode().(PropertyIdentifier).getValue()
}

string inferNameFromContext(Node context) {
  exists(AssignmentExpression assign |
    context = assign.getRight() and
    result = inferNameFromNode(assign.getLeft())
  )
  or
  exists(Pair pair |
    context = pair.getValue() and
    result = pair.getKey().(PropertyIdentifier).getValue()
  )
}
