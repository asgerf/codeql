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
   *   shorthand for `isAfterValueMatches`.
   */
  ValueFilter truthyCondition();

  /**
   * Gets the set of values resulting in the "true" outcome of the given condition.
   *
   * If not specified for a given condition, `truthyCondition()` is used for that condition.
   */
  ValueFilter getSpecialConditionFilter(L::AstNode node);
}

module MakeLanguageCommon<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  private import L
  private import C

  /**
   * Gets the set of values resulting in the "true" outcome of the given condition.
   */
  pragma[nomagic]
  ValueFilter getConditionFilter(AstNode node) {
    isCondition(node) and
    (
      result = getSpecialConditionFilter(node)
      or
      not exists(getSpecialConditionFilter(node)) and
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
      result = getSpecialConditionFilter(node)
      or
      not exists(getSpecialConditionFilter(node)) and
      result = truthyCondition()
    )
  }
}
