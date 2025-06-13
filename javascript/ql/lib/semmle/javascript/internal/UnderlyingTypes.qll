/**
 * Provides name resolution and propagates type information.
 */

private import javascript
private import semmle.javascript.internal.NameResolution::NameResolution

/**
 * Provides name resolution and propagates type information.
 */
module UnderlyingTypes {
  private predicate subtypeStep(Node node1, Node node2) {
    exists(ClassOrInterface cls |
      (
        node1 = cls.getSuperClass() or
        node1 = cls.getASuperInterface()
      ) and
      node2 = cls
    )
  }

  predicate underlyingTypeStep(Node node1, Node node2) {
    exists(UnionOrIntersectionTypeExpr type |
      node1 = type.getAnElementType() and
      node2 = type
    )
    or
    exists(ReadonlyTypeExpr type |
      node1 = type.getElementType() and
      node2 = type
    )
    or
    exists(OptionalTypeExpr type |
      node1 = type.getElementType() and
      node2 = type
    )
    or
    exists(GenericTypeExpr type |
      node1 = type.getTypeAccess() and
      node2 = type
    )
    or
    exists(ExpressionWithTypeArguments e |
      node1 = e.getExpression() and
      node2 = e
    )
    or
    exists(JSDocUnionTypeExpr type |
      node1 = type.getAnAlternative() and
      node2 = type
    )
    or
    exists(JSDocNonNullableTypeExpr type |
      node1 = type.getTypeExpr() and
      node2 = type
    )
    or
    exists(JSDocNullableTypeExpr type |
      node1 = type.getTypeExpr() and
      node2 = type
    )
    or
    exists(JSDocAppliedTypeExpr type |
      node1 = type.getHead() and
      node2 = type
    )
    or
    exists(JSDocOptionalParameterTypeExpr type |
      node1 = type.getUnderlyingType() and
      node2 = type
    )
  }

  predicate nodeHasUnderlyingType(Node node, string mod, string name) {
    nodeRefersToTypeName(node, mod, name)
    or
    exists(Node mid | nodeHasUnderlyingType(mid, mod, name) |
      TypeFlow::step(mid, node)
      or
      underlyingTypeStep(mid, node)
      or
      subtypeStep(mid, node)
    )
  }

  pragma[nomagic]
  predicate nodeHasUnderlyingType(Node node, string name) {
    nodeHasUnderlyingType(node, "global", name)
  }

  predicate nodeHasUnderlyingClassType(Node node, DataFlow::ClassNode cls) {
    node = cls.getAstNode()
    or
    exists(string name |
      classHasGlobalName(cls, name) and
      nodeHasUnderlyingType(node, name)
    )
    or
    exists(Node mid | nodeHasUnderlyingClassType(mid, cls) |
      TypeFlow::step(mid, node)
      or
      underlyingTypeStep(mid, node)
      // Note: unlike for external types, we do not use subtype steps here.
      // The caller is responsible for handling the class hierarchy.
    )
  }

  /**
   * Holds if `node` is a type with the given type parameter as an underlying type.
   *
   * For example:
   * ```ts
   * interface Foo<T> {
   *   f: T | null;
   * }
   * ```
   * The type `T | null` above has the type parameter `T` as an underlying type.
   */
  pragma[nomagic]
  predicate nodeHasUnderlyingTypeParameterType(Node node, TypeParameter typeParam) {
    node = getATypeParameterAccess(typeParam)
    or
    exists(Node mid | nodeHasUnderlyingTypeParameterType(mid, typeParam) |
      TypeFlow::step(mid, node)
      or
      underlyingTypeStep(mid, node)
    )
  }
}
