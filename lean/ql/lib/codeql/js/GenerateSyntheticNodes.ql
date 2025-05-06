private import GeneratedAst::JS

predicate shouldSynthesize(AstNode node, string tag) {
  exists(AugmentedAssignmentExpression asn | node = asn.getLeft() and tag = "lvalue")
  or
  exists(UpdateExpression update | node = update.getArgument() and tag = "value")
}

newtype TFreshNode = MkFreshNode(AstNode parent, string tag) { shouldSynthesize(parent, tag) }

module Fresh = QlBuiltins::NewEntity<TFreshNode>;

class TNewEntity = Fresh::EntityId;

class NewEntity extends TNewEntity {
  string toString() { none() }
}

query predicate js_synthetic_node_def(NewEntity child, AstNode parent, string tag) {
  child = Fresh::map(MkFreshNode(parent, tag))
}
