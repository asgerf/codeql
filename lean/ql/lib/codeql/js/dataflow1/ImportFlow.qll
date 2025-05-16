private import All

/**
 * Flow rules for array literals and their spread elements.
 */
class ImportFlow extends Stage1 {
  override predicate readStep(Node node1, ContentSet contents, Node node2) {
    exists(ImportStatement stmt, ImportSpecifier spec |
      node1 = stmt.getImportedModuleNode() and
      spec = stmt.getASpecifier() and
      contents = getContentSetFromKey(spec.getName())
    |
      node2 = getLValueNode(spec.getAlias())
      or
      not exists(spec.getAlias()) and
      node2 = getLValueNode(spec.getName())
    )
  }

  override predicate valueStep(Node node1, Node node2) {
    exists(ImportStatement stmt, AstNode spec |
      node1 = stmt.getImportedModuleNode() and
      spec = stmt.getASpecifier()
    |
      node2 = getLValueNode(spec.(NamespaceImport).getChild())
      or
      node2 = getLValueNode(spec.(Identifier)) // default import
    )
  }
}
