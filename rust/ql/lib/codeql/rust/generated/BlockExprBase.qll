// generated by codegen
/**
 * This module provides the generated definition of `BlockExprBase`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.Expr
import codeql.rust.elements.Stmt

/**
 * INTERNAL: This module contains the fully generated definition of `BlockExprBase` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::BlockExprBase` class directly.
   * Use the subclass `BlockExprBase`, where the following predicates are available.
   */
  class BlockExprBase extends Synth::TBlockExprBase, Expr {
    /**
     * Gets the `index`th statement of this block expression base (0-based).
     */
    Stmt getStatement(int index) {
      result =
        Synth::convertStmtFromRaw(Synth::convertBlockExprBaseToRaw(this)
              .(Raw::BlockExprBase)
              .getStatement(index))
    }

    /**
     * Gets any of the statements of this block expression base.
     */
    final Stmt getAStatement() { result = this.getStatement(_) }

    /**
     * Gets the number of statements of this block expression base.
     */
    final int getNumberOfStatements() { result = count(int i | exists(this.getStatement(i))) }

    /**
     * Gets the tail of this block expression base, if it exists.
     */
    Expr getTail() {
      result =
        Synth::convertExprFromRaw(Synth::convertBlockExprBaseToRaw(this)
              .(Raw::BlockExprBase)
              .getTail())
    }

    /**
     * Holds if `getTail()` exists.
     */
    final predicate hasTail() { exists(this.getTail()) }
  }
}
