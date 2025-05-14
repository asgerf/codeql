private import codeql.util.Location
private import codeql.shared.LanguageBase

signature module LanguageCommonSig<LocationSig Location, LanguageBaseSig<Location> L> {
  class CfgScope extends L::AstNode;

  CfgScope getCfgScope(L::AstNode node);

  class ValueFilter {
    /**
     * Gets the filter matching exactly the values that this filter does not match.
     */
    ValueFilter negate();

    /**
     * Gets a value filter matching the intersection of `this` and `other`, if any.
     *
     * Has no result if the set of values is empty.
     */
    ValueFilter intersect(ValueFilter other);
  }

  /**
   * Gets the value filter representing "truthy" values.
   *
   * Typically this filter corresponds to the set of values that would cause an if-statement to take its "then" branch.
   *
   * Concretely, has the following effects:
   * - If `getConditionFilter` has no result for a given condition node, this filter is used as the value filter for that condition.
   * - `CfgNode.isAfterTrue(node)` and `CfgNode.isAfterFalse(node)` refer to this condition under the hood, as more readable
   *   shorthand for the 2-argument call `isAfter(node, filter)`.
   */
  ValueFilter truthyCondition();

  /**
   * Gets the set of values resulting in the "true" outcome of the given condition.
   *
   * If not specified for a given condition, it is taken from  `truthyCondition()` is used for that condition.
   */
  ValueFilter getSpecialConditionFilter(L::AstNode node);

  predicate logicalValueStep(L::AstNode node1, L::AstNode node2);
}

module MakeLanguageCommon<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  private import L
  private import C

  private ValueFilter getSpecialConditionFilterEx(AstNode node) {
    result = getSpecialConditionFilter(node)
    or
    exists(AstNode condition |
      logicalValueStep(node, condition) and
      result = getSpecialConditionFilter(condition)
    )
  }

  /**
   * Gets the set of values resulting in the "true" outcome of the given condition.
   */
  pragma[nomagic]
  ValueFilter getConditionFilter(AstNode node) {
    isCondition(node) and
    (
      result = getSpecialConditionFilterEx(node)
      or
      not exists(getSpecialConditionFilterEx(node)) and
      result = truthyCondition()
    )
  }

  /**
   * Gets the set of values resulting in the "true" outcome of the condition in the L-value associated with `node`.
   */
  pragma[nomagic]
  ValueFilter getLValueConditionFilter(AstNode node) {
    isConditionInLValue(node) and
    (
      result = getSpecialConditionFilterEx(node)
      or
      not exists(getSpecialConditionFilterEx(node)) and
      result = truthyCondition()
    )
  }

  signature module ResolveVariablesSig {
    class VariableReference extends AstNode {
      string getName();
    }

    /**
     * Holds if `ref` is a declaration of a variable that will exist in the given `scope`.
     */
    predicate variableDeclaredInScope(VariableReference ref, AstNode scope);

    /**
     * Holds if a variable named `name` is implicitly in scope in the given `scope`.
     */
    predicate variableImplicitlyInScope(string name, AstNode scope);

    /**
     * Holds the variable `ref` should begin its lookup in `scope` instead of its parent node.
     *
     * For example, the `this` variable in an instance field initializer might need to be resolved
     * relative to a constructor body.
     *
     * If `scope` declares a variable with the name of `ref`, then `scope` is guaranteed to be the
     * scope that `ref` ultimately resolves to. This can thus be used to take full control of scope resolution for
     * for specific types of references.
     */
    default predicate lookupStartsAt(VariableReference ref, AstNode scope) { none() }
  }

  module ResolveVariables<ResolveVariablesSig Res> {
    private import Res

    final private class FinalAstNode = AstNode;

    private predicate variableInScope(string name, AstNode scope) {
      exists(VariableReference ref |
        variableDeclaredInScope(ref, scope) and
        name = ref.getName()
      )
      or
      variableImplicitlyInScope(name, scope)
    }

    private class VariableScope extends FinalAstNode {
      VariableScope() { variableInScope(_, this) }

      predicate hasVariable(string name) { variableInScope(name, this) }

      AstNode getANodeInScope() {
        result = this
        or
        result.getParent() = this.getANodeInScope() and
        not result instanceof VariableScope
      }

      VariableScope getParentScope() { result.getANodeInScope() = this.getParent() }
    }

    final private class FinalVariableReference = VariableReference;

    /**
     * An access to a variable that is not a declaration.
     */
    class VariableAccess extends FinalVariableReference {
      VariableAccess() { not variableDeclaredInScope(this, _) }

      LocalVariable getVariable() { this = result.getAnAccess() }
    }

    /**
     * An identifier that declares a variable.
     */
    class VariableDeclarationSite extends FinalVariableReference {
      VariableDeclarationSite() { variableDeclaredInScope(this, _) }

      LocalVariable getVariable() { this = result.getADeclarationSite() }
    }

    private predicate tryResolveToScope(VariableAccess ref, string name, VariableScope scope) {
      ref.getName() = name and
      (
        lookupStartsAt(ref, scope)
        or
        not lookupStartsAt(ref, _) and
        scope.getANodeInScope() = ref
      )
      or
      exists(VariableScope innerScope |
        tryResolveToScope(ref, name, innerScope) and
        not innerScope.hasVariable(name) and
        scope = innerScope.getParentScope()
      )
    }

    private predicate resolveToScope(VariableAccess ref, string name, VariableScope scope) {
      tryResolveToScope(ref, name, scope) and
      scope.hasVariable(name)
    }

    private newtype TLocalVariable =
      MkLocalVariable(AstNode scope, string name) { variableInScope(name, scope) }

    class LocalVariable extends TLocalVariable {
      private AstNode scope;
      private string name;

      LocalVariable() { this = MkLocalVariable(scope, name) }

      AstNode getScope() { result = scope }

      string getName() { result = name }

      string toString() { result = name }

      VariableAccess getAnAccess() { resolveToScope(result, name, scope) }

      VariableDeclarationSite getADeclarationSite() {
        variableDeclaredInScope(result, scope) and
        result.getName() = name
      }

      VariableReference getAReference() {
        result = this.getAnAccess() or result = this.getADeclarationSite()
      }

      CfgScope getCfgScope() {
        result = scope
        or
        not scope instanceof CfgScope and
        result = getCfgScope(scope)
      }

      predicate isCaptured() { this.isCapturingAccess(_) }

      predicate isCapturingAccess(VariableAccess access) {
        access = this.getAnAccess() and getCfgScope(access) != this.getCfgScope()
      }

      Location getLocation() {
        result =
          min(Location loc |
            loc = this.getADeclarationSite().getLocation()
          |
            loc order by loc.getStartLine(), loc.getStartColumn()
          )
        or
        not exists(this.getADeclarationSite()) and
        result = scope.getLocation()
      }
    }

    module Debug {
      query predicate unresolvedVariableAccesses(VariableAccess access) {
        not exists(access.getVariable())
      }

      query predicate ambiguousToString(LocalVariable v) { count(v.toString()) != 1 }

      query predicate ambiguousLocation(LocalVariable v) { count(v.getLocation()) != 1 }

      query predicate ambiguousCfgScope(LocalVariable v) { count(v.getCfgScope()) != 1 }
    }
  }
}
