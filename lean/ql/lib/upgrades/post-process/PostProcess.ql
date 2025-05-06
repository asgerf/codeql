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

class TOldOrNewNode = @js_ast_node or Fresh::EntityId;

class OldOrNewNode extends TOldOrNewNode {
  OldOrNewNode() {
    // remove pre-existing synthetic nodes in case re-running post-processing after an upgrade
    not this instanceof @js_synthetic_node
  }

  string toString() { none() }
}

class Location extends @location_default {
  string toString() { none() }
}

query predicate js_synthetic_node_def(FreshEntity id, AstNode parent, string tag) {
  id = Fresh::map(MkFresh(parent, tag))
}

query predicate new_js_ast_node_location(OldOrNewNode id, Location location) {
  js_ast_node_location(id, location)
  or
  exists(AstNode node |
    js_synthetic_node_def(id, node, _) and
    js_ast_node_location(node, location)
  )
}
