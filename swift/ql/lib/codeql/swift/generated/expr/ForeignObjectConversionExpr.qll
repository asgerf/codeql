// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `ForeignObjectConversionExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.ImplicitConversionExprImpl::Impl as ImplicitConversionExprImpl

/**
 * INTERNAL: This module contains the fully generated definition of `ForeignObjectConversionExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::ForeignObjectConversionExpr` class directly.
   * Use the subclass `ForeignObjectConversionExpr`, where the following predicates are available.
   */
  class ForeignObjectConversionExpr extends Synth::TForeignObjectConversionExpr,
    ImplicitConversionExprImpl::ImplicitConversionExpr
  {
    override string getAPrimaryQlClass() { result = "ForeignObjectConversionExpr" }
  }
}
