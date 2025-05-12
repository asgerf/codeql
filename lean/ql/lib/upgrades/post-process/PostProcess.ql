private import codeql.js.base.GeneratedAst
private import codeql.js.base.LanguageBase
private import JS

private predicate shouldSynthesize(AstNode node, string tag) {
  LanguageBase::synthesizeNode(node, tag)
  or
  (
    LanguageBase::isInPureLValuePosition(node)
    or
    LanguageBase::isInImpureLValuePosition(node)
  ) and
  tag = ["lvalue", "lvalue-end"]
  or
  LanguageBase::isCondition(node) and tag = ["condition-true", "condition-false"]
  or
  LanguageBase::isConditionInLValue(node) and tag = ["lvalue-true", "lvalue-false"]
  or
  LanguageBase::needsCfg(node) and
  not node instanceof Token and
  tag = "cfg-begin"
  or
  LanguageBase::isCfgScope(node) and
  tag = ["cfg-enter", "cfg-exit"]
}

module L {
  signature class LocationSig;

  // This is needed as replacement for the import in GeneratedAst.qll
  class Location extends @location_default {
    string toString() { none() }
  }
}

newtype TFresh = MkFresh(AstNode node, string tag) { shouldSynthesize(node, tag) }

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
