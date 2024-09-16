// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `InOutType`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.type.Type
import codeql.swift.elements.type.TypeImpl::Impl as TypeImpl

/**
 * INTERNAL: This module contains the fully generated definition of `InOutType` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::InOutType` class directly.
   * Use the subclass `InOutType`, where the following predicates are available.
   */
  class InOutType extends Synth::TInOutType, TypeImpl::Type {
    override string getAPrimaryQlClass() { result = "InOutType" }

    /**
     * Gets the object type of this in out type.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Type getImmediateObjectType() {
      result =
        Synth::convertTypeFromRaw(Synth::convertInOutTypeToRaw(this)
              .(Raw::InOutType)
              .getObjectType())
    }

    /**
     * Gets the object type of this in out type.
     */
    final Type getObjectType() {
      exists(Type immediate |
        immediate = this.getImmediateObjectType() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }
  }
}
