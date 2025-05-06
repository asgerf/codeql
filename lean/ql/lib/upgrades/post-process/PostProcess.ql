class AstNode extends @js_ast_node {
  string toString() { none() }
}

predicate needsSyntheticNode(AstNode node, string tag) {
  tag = "lvalue" and
  (
    js_augmented_assignment_expression_def(_, node, _, _)
    or
    js_update_expression_def(_, node, _)
  )
  or
  tag = "binary-operator" and
  js_augmented_assignment_expression_def(node, _, _, _)
}

newtype TFresh = MkFresh(AstNode node, string tag) { needsSyntheticNode(node, tag) }

module Fresh = QlBuiltins::NewEntity<TFresh>;

class FreshEntity extends Fresh::EntityId {
  string toString() { none() }
}

query predicate js_synthetic_node_def(FreshEntity id, AstNode parent, string tag) {
  id = Fresh::map(MkFresh(parent, tag))
}
