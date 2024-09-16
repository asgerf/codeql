// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `BindOptionalExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.Expr
import codeql.swift.elements.expr.ExprImpl::Impl as ExprImpl

/**
 * INTERNAL: This module contains the fully generated definition of `BindOptionalExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::BindOptionalExpr` class directly.
   * Use the subclass `BindOptionalExpr`, where the following predicates are available.
   */
  class BindOptionalExpr extends Synth::TBindOptionalExpr, ExprImpl::Expr {
    override string getAPrimaryQlClass() { result = "BindOptionalExpr" }

    /**
     * Gets the sub expression of this bind optional expression.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Expr getImmediateSubExpr() {
      result =
        Synth::convertExprFromRaw(Synth::convertBindOptionalExprToRaw(this)
              .(Raw::BindOptionalExpr)
              .getSubExpr())
    }

    /**
     * Gets the sub expression of this bind optional expression.
     */
    final Expr getSubExpr() {
      exists(Expr immediate |
        immediate = this.getImmediateSubExpr() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }
  }
}
