// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `AbstractStorageDecl`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.decl.Accessor
import codeql.swift.elements.decl.ValueDeclImpl::Impl as ValueDeclImpl

/**
 * INTERNAL: This module contains the fully generated definition of `AbstractStorageDecl` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::AbstractStorageDecl` class directly.
   * Use the subclass `AbstractStorageDecl`, where the following predicates are available.
   */
  class AbstractStorageDecl extends Synth::TAbstractStorageDecl, ValueDeclImpl::ValueDecl {
    /**
     * Gets the `index`th accessor of this abstract storage declaration (0-based).
     */
    Accessor getAccessor(int index) {
      result =
        Synth::convertAccessorFromRaw(Synth::convertAbstractStorageDeclToRaw(this)
              .(Raw::AbstractStorageDecl)
              .getAccessor(index))
    }

    /**
     * Gets any of the accessors of this abstract storage declaration.
     */
    final Accessor getAnAccessor() { result = this.getAccessor(_) }

    /**
     * Gets the number of accessors of this abstract storage declaration.
     */
    final int getNumberOfAccessors() { result = count(int i | exists(this.getAccessor(i))) }
  }
}
