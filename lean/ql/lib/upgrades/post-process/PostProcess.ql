private import codeql.js.base.GeneratedAst
private import codeql.js.base.LanguageBaseImpl as LanguageBaseImpl
private import codeql.Locations
private import codeql.shared.LanguageBase
private import MakePostProcessor<Location, LanguageBaseImpl::LanguageBase>

private string getAPrefix(string fullTag) {
  shouldSynthesize(_, fullTag) and
  result = [fullTag, fullTag.prefix(fullTag.indexOf("/"))]
}

private class TagString extends string {
  TagString() { this = getAPrefix(_) }

  private int lastSlash() { result = max(this.indexOf("/")) }

  predicate isCons(TagString prefix, string suffix) {
    exists(int slashIndex |
      slashIndex = this.lastSlash() and
      prefix = this.prefix(slashIndex) and
      suffix = this.suffix(slashIndex + 1)
    )
  }
}

newtype TFresh =
  MkFresh(AstNode node, TagString tag) {
    exists(string fullTag |
      shouldSynthesize(node, fullTag) and
      tag = getAPrefix(fullTag)
    )
  }

module Fresh = QlBuiltins::NewEntity<TFresh>;

class FreshEntity extends Fresh::EntityId {
  string toString() { none() }
}

class TOldOrNewNode = @js_ast_node or Fresh::EntityId;

class OldOrNewNode extends TOldOrNewNode {
  string toString() { none() }
}

module QueryPredicates {
  query predicate new_js_synthetic_node_def(FreshEntity id, OldOrNewNode parent, string tag) {
    exists(AstNode astNode, TagString fullTag | id = Fresh::map(MkFresh(astNode, fullTag)) |
      exists(TagString prefix, string suffix |
        fullTag.isCons(prefix, suffix) and
        parent = Fresh::map(MkFresh(astNode, prefix)) and
        tag = suffix
      )
      or
      not fullTag.isCons(_, _) and
      parent = astNode and
      tag = fullTag
    )
  }

  query predicate new_js_ast_node_location(OldOrNewNode id, L::Location location) {
    not id instanceof @js_synthetic_node and
    js_ast_node_location(id, location)
    or
    exists(AstNode astNode |
      id = Fresh::map(MkFresh(astNode, _)) and
      js_ast_node_location(astNode, location)
    )
  }
}
