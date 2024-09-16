// generated by codegen
/**
 * This module provides the generated definition of `BreakExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.Expr
import codeql.rust.elements.Label

/**
 * INTERNAL: This module contains the fully generated definition of `BreakExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * A break expression. For example:
   * ```
   * loop {
   *     if not_ready() {
   *         break;
   *      }
   * }
   * ```
   * ```
   * let x = 'label: loop {
   *     if done() {
   *         break 'label 42;
   *     }
   * };
   * ```
   * INTERNAL: Do not reference the `Generated::BreakExpr` class directly.
   * Use the subclass `BreakExpr`, where the following predicates are available.
   */
  class BreakExpr extends Synth::TBreakExpr, Expr {
    override string getAPrimaryQlClass() { result = "BreakExpr" }

    /**
     * Gets the expression of this break expression, if it exists.
     */
    Expr getExpr() {
      result =
        Synth::convertExprFromRaw(Synth::convertBreakExprToRaw(this).(Raw::BreakExpr).getExpr())
    }

    /**
     * Holds if `getExpr()` exists.
     */
    final predicate hasExpr() { exists(this.getExpr()) }

    /**
     * Gets the label of this break expression, if it exists.
     */
    Label getLabel() {
      result =
        Synth::convertLabelFromRaw(Synth::convertBreakExprToRaw(this).(Raw::BreakExpr).getLabel())
    }

    /**
     * Holds if `getLabel()` exists.
     */
    final predicate hasLabel() { exists(this.getLabel()) }
  }
}
