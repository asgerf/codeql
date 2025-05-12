private import All

private AstNode getParentOverride(AstNode node) {
  exists(FunctionDeclaration decl |
    // The name of a function declaration belongs to the outer scope
    node = decl.getName() and
    result = decl.getParent()
  )
  // TODO: instance field initializers go inside the class constructor
}

private AstNode getParentForCfgScope(AstNode node) {
  result = getParentOverride(node)
  or
  not exists(getParentOverride(node)) and
  result = node.getParent()
}

/**
 * Gets the nearest strictly enclosing CFG scope.
 *
 * If `node` is itself a CFG scope, this gets the outer scope, not the `node` itself.
 */
pragma[nomagic]
CfgScope getCfgScope(AstNode node) {
  exists(AstNode parent | parent = getParentForCfgScope(node) |
    result = parent
    or
    not parent instanceof CfgScope and
    result = getCfgScope(parent)
  )
}

final class CfgScope = CfgScopeImpl;

abstract private class CfgScopeImpl extends AstNode { }

private class ProgramAsCfgScope extends CfgScopeImpl instanceof Program { }

private class FunctionAsCfgScope extends CfgScopeImpl instanceof Function { }
