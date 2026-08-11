private import unified
private import codeql.unified.internal.StaticNameBinding
private import codeql.unified.internal.NameBindingPlugin

private Expr getAnImportedPrefix(ImportDeclaration imprt) {
  result = imprt.getImportedExpr()
  or
  result = getAnImportedPrefix(imprt).(MemberAccessExpr).getBase()
}

ModuleScopeRepr getImportedModule(ImportDeclaration imprt) {
  exists(NamespaceNode node |
    node.isModuleScopeNode(result) and
    node.ref().asIdentifier() = getAnImportedPrefix(imprt).(NameExpr).getIdentifier()
  )
}
