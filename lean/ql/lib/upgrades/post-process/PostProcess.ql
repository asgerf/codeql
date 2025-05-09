private import codeql.js.GeneratedAst
private import codeql.js.PostProcessing
private import JS

module L {
  // This is needed as replacement for the import in GeneratedAst.qll
  class Location extends @location_default {
    string toString() { none() }
  }
}

newtype TFresh =
  MkFresh(AstNode node, string tag) { PostProcessing::shouldSynthesizeNode(node, tag) }

module Fresh = QlBuiltins::NewEntity<TFresh>;

class FreshEntity extends Fresh::EntityId {
  string toString() { none() }
}

class TOldOrNewNode = @js_ast_node or Fresh::EntityId;

class OldOrNewNode extends TOldOrNewNode {
  string toString() { none() }
}

query predicate new_js_synthetic_node_def(FreshEntity id, AstNode parent, string tag) {
  id = Fresh::map(MkFresh(parent, tag))
}

query predicate new_js_ast_node_location(OldOrNewNode id, L::Location location) {
  not id instanceof @js_synthetic_node and
  js_ast_node_location(id, location)
  or
  exists(AstNode node |
    new_js_synthetic_node_def(id, node, _) and
    js_ast_node_location(node, location)
  )
}
