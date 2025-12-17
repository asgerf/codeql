private import All

/**
 * A `StatementBlock` or `Program`.
 */
final class BlockScope extends AstNode {
  BlockScope() { this instanceof StatementBlock or this instanceof Program }
}

private BlockScope getEnclosingBlockScope(AstNode node) {
  result = node
  or
  not node instanceof BlockScope and
  result = getEnclosingBlockScope(node.getParent())
}

private predicate isInDeclarationContext(AstNode node, AstNode scope) {
  exists(VariableDeclarator decl |
    node = decl.getName() and
    if decl.getParent() instanceof LexicalDeclaration
    then scope = getEnclosingBlockScope(decl)
    else scope = getEnclosingCallable(decl)
  )
  or
  exists(ForInStatement stmt | node = stmt.getLeft() |
    stmt.getKind().(Token).getValue() = "var" and
    scope = getEnclosingCallable(stmt)
    or
    stmt.getKind().(Token).getValue() = ["let", "const"] and
    scope = stmt
  )
  or
  exists(FunctionDeclaration decl |
    // note: this refers to the outer scope (as it should) due to how getEnclosingCallable is defined
    node = decl.getName() and
    scope = getEnclosingCallable(node)
  )
  or
  exists(FunctionExpression fun |
    node = fun.getName() and
    scope = fun
  )
  or
  exists(Class cls |
    node = cls.getName() and
    scope = cls
  )
  or
  exists(ClassDeclaration cls |
    node = cls.getName() and
    scope = getEnclosingBlockScope(cls)
  )
  or
  exists(CatchClause catch |
    node = catch.getParameter() and
    scope = catch
  )
  or
  exists(Parameter parameter |
    node = parameter and
    scope = getEnclosingCallable(parameter)
  )
  or
  exists(AstNode parent | isInDeclarationContext(parent, scope) |
    node = parent.(ObjectPattern).getChild(_)
    or
    node = parent.(ArrayPattern).getChild(_)
    or
    node = parent.(PairPattern).getValue()
    or
    node = parent.(RestPattern).getChild()
    or
    node = parent.(AssignmentPattern).getLeft()
  )
}

final class VariableReference = VariableReferenceImpl;

abstract private class VariableReferenceImpl extends AstNode {
  abstract string getName();

  final LocalVariable getVariable() { result.getAReference() = this }
}

private class IdentifierAsVarRef extends VariableReferenceImpl instanceof Identifier {
  override string getName() { result = super.getValue() }
}

private class ShorthandPropertyIdentifierAsVarRef extends VariableReferenceImpl instanceof ShorthandPropertyIdentifier
{
  override string getName() { result = super.getValue() }
}

private class ShorthandPropertyIdentifierPatternAsVarRef extends VariableReferenceImpl instanceof ShorthandPropertyIdentifierPattern
{
  override string getName() { result = super.getValue() }
}

private class ThisAsVarRef extends VariableReferenceImpl instanceof This {
  override string getName() { result = "this" }
}

private class ThisParameterAsVarRef extends VariableReferenceImpl {
  ThisParameterAsVarRef() { this = any(Callable c).getThisParameter() }

  override string getName() { result = "this" }
}

private module ResolveVariableConfig implements ResolveVariablesSig {
  final class VariableReference = VariableReferenceImpl;

  predicate variableDeclaredInScope(VariableReference declarationSite, AstNode scope) {
    isInDeclarationContext(declarationSite, scope)
  }

  predicate variableImplicitlyInScope(string name, AstNode scope) {
    scope instanceof Callable and
    not scope instanceof ArrowFunction and
    name = ["this", "arguments"]
  }
}

private import ResolveVariables<ResolveVariableConfig> as Res

class LocalVariable = Res::LocalVariable;

class LocalVariableAccess extends Res::VariableAccess {
  LocalVariableAccess() { exists(this.getVariable()) }
}

/**
 * An access to a variable with no declaration in scope, either because it is global
 * or because a module system implicitly put it in scope.
 */
class UnresolvedVariableAccess extends VariableReference instanceof Res::VariableAccess {
  UnresolvedVariableAccess() { not exists(this.getVariable()) }
}
