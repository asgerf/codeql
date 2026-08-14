/**
 * @name Unused variable
 * @description Unused variables may be an indication that the code is incomplete or has a typo.
 * @kind problem
 * @problem.severity recommendation
 * @id unified/unused-variable
 * @precision high
 */

private import unified
private import codeql.unified.internal.LocalNameBinding

private predicate isUnusedLocal(LocalName local) {
  not exists(PotentialLocalNameAccess access |
    access.getLocalName() = local and
    not access.isDeclarationSite()
  )
}

private predicate isUnusedNameDecl(NameDeclaration decl) {
  isUnusedLocal(decl.getLocalName()) and
  not decl.getName().regexpMatch("_.*") and // Ignore if starting with underscore
  not decl.getDeclaration() = any(ClassLikeDeclaration cls).getAMember() and
  not decl.getDeclaration() = any(TopLevel t).getBody().getAStmt()
}

from NameDeclaration decl
where isUnusedNameDecl(decl)
select decl, "Unused variable '" + decl.getName() + "'"
