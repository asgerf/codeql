// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `PackExpansionExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.Expr
import codeql.swift.elements.expr.ExprImpl::Impl as ExprImpl

/**
 * INTERNAL: This module contains the fully generated definition of `PackExpansionExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * A pack expansion expression.
   *
   * In the following example, `repeat each t` on the second line is the pack expansion expression:
   * ```
   * func makeTuple<each T>(_ t: repeat each T) -> (repeat each T) {
   *   return (repeat each t)
   * }
   * ```
   *
   * More details:
   * https://github.com/apple/swift-evolution/blob/main/proposals/0393-parameter-packs.md
   * INTERNAL: Do not reference the `Generated::PackExpansionExpr` class directly.
   * Use the subclass `PackExpansionExpr`, where the following predicates are available.
   */
  class PackExpansionExpr extends Synth::TPackExpansionExpr, ExprImpl::Expr {
    override string getAPrimaryQlClass() { result = "PackExpansionExpr" }

    /**
     * Gets the pattern expression of this pack expansion expression.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Expr getImmediatePatternExpr() {
      result =
        Synth::convertExprFromRaw(Synth::convertPackExpansionExprToRaw(this)
              .(Raw::PackExpansionExpr)
              .getPatternExpr())
    }

    /**
     * Gets the pattern expression of this pack expansion expression.
     */
    final Expr getPatternExpr() {
      exists(Expr immediate |
        immediate = this.getImmediatePatternExpr() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }
  }
}
