private import All

string getStringValueFromNode(AstNode node) { result = node.(StringFragment).getValue() or none() }

int getIntValueFromNode(AstNode node) { result = node.(Number).getValue().toInt() or none() }

ContentSet getContentSetFromKey(AstNode key) {
  result.asPropertyName() = key.(PropertyIdentifier).getValue() or
  result.asPropertyName() = getStringValueFromNode(key) or
  result = ContentSet::arrayElementKnown(getIntValueFromNode(key))
}

AstNode getPostUpdate(AstNode node) { result = node } // TODO

predicate isLikelyArrayAccess(SubscriptExpression e) {
  none() // TODO
}

string inferNameFromNode(AstNode node) {
  result = node.(Identifier).getValue()
  or
  result = node.(PropertyIdentifier).getValue()
  or
  result = node.(PropAccess).getPropertyNameNode().(PropertyIdentifier).getValue()
}

string inferNameFromContext(AstNode context) {
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
