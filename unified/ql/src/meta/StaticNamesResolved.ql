/**
 * @name Resolved static name references
 * @description Static name references that could be resolved to a target
 * @kind problem
 * @problem.severity recommendation
 * @id unified/meta/static-names-resolved
 * @tags meta
 * @precision very-low
 */

private import unified
private import codeql.unified.internal.StaticNameBinding
private import codeql.unified.internal.NameBindingPlugin

AstNode getResolutionTarget(Identifier id) {
  exists(NameBindingNode node | node.isIdentifier(id) |
    trackNameDeclaration(result) = node and
    exists(ClassLikeDeclaration cls |
      not cls.hasModifier("extension") and // don't treat extensions as the true resolution target
      result = cls.getName()
    )
    or
    exists(NamespaceNode ns |
      ns.isModuleScopeNode(result) and
      ns.ref() = node
    )
  )
}

from Identifier id, AstNode target
where target = getResolutionTarget(id)
select id, "Reference to $@", target, target.toString()
