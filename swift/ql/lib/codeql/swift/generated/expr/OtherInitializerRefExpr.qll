// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `OtherInitializerRefExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.ExprImpl::Impl as ExprImpl
import codeql.swift.elements.decl.Initializer

/**
 * INTERNAL: This module contains the fully generated definition of `OtherInitializerRefExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::OtherInitializerRefExpr` class directly.
   * Use the subclass `OtherInitializerRefExpr`, where the following predicates are available.
   */
  class OtherInitializerRefExpr extends Synth::TOtherInitializerRefExpr, ExprImpl::Expr {
    override string getAPrimaryQlClass() { result = "OtherInitializerRefExpr" }

    /**
     * Gets the initializer of this other initializer reference expression.
     */
    Initializer getInitializer() {
      result =
        Synth::convertInitializerFromRaw(Synth::convertOtherInitializerRefExprToRaw(this)
              .(Raw::OtherInitializerRefExpr)
              .getInitializer())
    }
  }
}
