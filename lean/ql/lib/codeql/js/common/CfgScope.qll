private import All

/**
 * Gets the nearest enclosing function or program, possibly `node` itself.
 */
pragma[nomagic]
CfgScope getCfgScope(AstNode node) {
  result = node
  or
  not node instanceof CfgScope and
  result = getCfgScope(node.getParent())
}

final class CfgScope = CfgScopeImpl;

abstract private class CfgScopeImpl extends AstNode { }

private class ProgramAsCfgScope extends CfgScopeImpl instanceof Program { }

private class FunctionAsCfgScope extends CfgScopeImpl instanceof Function { }
