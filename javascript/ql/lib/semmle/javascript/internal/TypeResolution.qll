private import javascript
private import semmle.javascript.internal.NameResolution::NameResolution
private import semmle.javascript.internal.UnderlyingTypes
private import semmle.javascript.dataflow.internal.sharedlib.SummaryTypeTracker as SummaryTypeTracker

module TypeResolution {
  predicate trackType = TypeFlow::TrackNode<TypeDefinition>::track/1;

  /**
   * Gets a node that has `fun` as an underlying type.
   *
   * We track through underlying types as an approximate way to handle calls to a type
   * that is a union/intersection involving functions.
   */
  Node trackUnderlyingFunctionType(Function fun) {
    result = fun
    or
    exists(Node mid | mid = trackUnderlyingFunctionType(fun) |
      TypeFlow::step(mid, result)
      or
      UnderlyingTypes::underlyingTypeStep(mid, result)
    )
  }

  /**
   * Gets the representative for the type containing the given member.
   *
   * For non-static members this is simply the enclosing type declaration.
   *
   * For static members we use the class's `Variable` as representative for the type of the class object.
   */
  private Node getMemberBase(MemberDeclaration member) {
    if member.isStatic()
    then result = member.getDeclaringClass().getVariable()
    else result = member.getDeclaringType()
  }

  /**
   * Holds if `host` is a type with a `content` of type `memberType`, not counting inherited members.
   */
  private predicate typeOwnMember(Node host, DataFlow::Content content, Node memberType) {
    exists(MemberDeclaration decl | host = getMemberBase(decl) |
      exists(FieldDeclaration field |
        decl = field and
        content.asPropertyName() = field.getName() and
        memberType = field.getTypeAnnotation()
      )
      or
      exists(MethodDeclaration method |
        decl = method and
        content.asPropertyName() = method.getName()
      |
        not method instanceof AccessorMethodDeclaration and
        memberType = method.getBody() // use the Function as representative for the function type
        or
        method instanceof GetterMethodDeclaration and
        memberType = method.getBody().getReturnTypeAnnotation()
      )
      or
      decl instanceof IndexSignature and
      memberType = decl.(IndexSignature).getBody().getReturnTypeAnnotation() and
      content.isUnknownArrayElement()
    )
    or
    // Ad-hoc support for array types. We don't support generics in general currently, we just special-case arrays and promises.
    content.isUnknownArrayElement() and
    (
      memberType = host.(ArrayTypeExpr).getElementType()
      or
      exists(GenericTypeExpr type |
        host = type and
        type.getTypeAccess().(LocalTypeAccess).getName() = ["Array", "ReadonlyArray"] and
        memberType = type.getTypeArgument(0)
      )
      or
      exists(JSDocAppliedTypeExpr type |
        host = type and
        type.getHead().(JSDocLocalTypeAccess).getName() = "Array" and
        memberType = type.getArgument(0)
      )
    )
    or
    content.isPromiseValue() and
    memberType = unwrapPromiseType(host)
  }

  /**
   * Holds if `host` is a type with a `content` of type `memberType`, possible due to inheritance.
   */
  private predicate typeMember(Node host, DataFlow::Content content, Node memberType) {
    typeOwnMember(host, content, memberType)
    or
    // Inherit members from base types
    not typeOwnMember(host, content, _) and
    exists(ClassOrInterface baseType | typeMember(baseType, content, memberType) |
      host.(ClassDefinition).getSuperClass() = trackClassValue(baseType)
      or
      host.(ClassOrInterface).getASuperInterface() = trackType(baseType)
    )
  }

  /** Gets a declared base type from a type declaration. */
  private Node getABaseType(Node typeDecl) {
    result = typeDecl.(ClassDefinition).getSuperClass()
    or
    result = typeDecl.(ClassOrInterface).getASuperInterface()
  }

  /**
   * Gets the declaration of the type referred to or instantiated by `typeRef`.
   */
  private Node getHeadTypeDecl(Node typeRef) {
    trackType(result) = typeRef
    or
    trackClassValue(result) = typeRef and
    typeRef = any(ClassDefinition cls).getSuperClass()
    or
    exists(TypeInstantiation instantiation | typeRef = trackTypeInstantiation(instantiation) |
      trackType(result) = instantiation.getHead()
      or
      trackClassValue(result) = instantiation.(ExpressionWithTypeArguments).getExpression()
    )
  }

  /** Gets a declared base type froma reference to a type */
  private Node getABaseTypeFromTypeRef(Node type) { result = getABaseType(getHeadTypeDecl(type)) }

  /**
   * Holds `use` refers to `host`, and `host` has type members.
   *
   * Currently steps through unions and intersections, which acts as a basic
   * approximation to the unions/intersection of objects.
   */
  private predicate typeMemberHostReaches(Node host, Node use) {
    typeMember(host, _, _) and
    use = host
    or
    exists(Node mid | typeMemberHostReaches(host, mid) |
      TypeFlow::step(mid, use)
      or
      UnderlyingTypes::underlyingTypeStep(mid, use)
    )
    or
    // The super-class of a class is a value, not a type, so we need to track classes here through the value graph.
    use = trackClassValue(host) and
    (
      use = any(ClassDefinition cls).getSuperClass()
      or
      use = any(ExpressionWithTypeArguments e).getExpression()
    )
  }

  /**
   * Holds if there is a read from from `object` to `member` that reads `contents`.
   */
  private predicate valueReadStep(Node object, DataFlow::ContentSet contents, Node member) {
    member.(PropAccess).accesses(object, contents.asPropertyName())
    or
    object.(ObjectPattern).getPropertyPatternByName(contents.asPropertyName()).getValuePattern() =
      member
    or
    member.(AwaitExpr).getOperand() = object and
    contents = DataFlow::ContentSet::promiseValue()
    or
    SummaryTypeTracker::basicLoadStep(object.(AST::ValueNode).flow(),
      member.(AST::ValueNode).flow(), contents)
    or
    exists(IndexExpr index |
      not exists(index.getPropertyName()) and
      object = index.getBase() and
      member = index and
      contents = DataFlow::ContentSet::arrayElement()
    )
  }

  predicate callTarget(InvokeExpr call, Function target) {
    exists(ClassDefinition cls |
      valueHasType(call.(NewExpr).getCallee(), trackClassValue(cls)) and
      target = cls.getConstructor().getBody()
    )
    or
    valueHasType(call.getCallee(), trackFunctionValue(target))
    or
    valueHasType(call.getCallee(), trackUnderlyingFunctionType(target)) and
    (
      call instanceof NewExpr and
      target = any(ConstructorTypeExpr t).getFunction()
      or
      call instanceof CallExpr and
      target = any(PlainFunctionTypeExpr t).getFunction()
    )
    or
    exists(InterfaceDefinition interface, CallSignature sig |
      valueHasType(call.getCallee(), trackType(interface)) and
      sig = interface.getACallSignature() and
      target = sig.getBody()
    |
      call instanceof NewExpr and
      sig instanceof ConstructorCallSignature
      or
      call instanceof CallExpr and
      sig instanceof FunctionCallSignature
    )
  }

  private predicate functionReturnType(Function func, Node returnType) {
    returnType = func.getReturnTypeAnnotation()
    or
    not exists(func.getReturnTypeAnnotation()) and
    exists(Function functionType |
      contextualType(func, trackUnderlyingFunctionType(functionType)) and
      returnType = functionType.getReturnTypeAnnotation()
    )
  }

  bindingset[name]
  private predicate isPromiseTypeName(string name) {
    name.regexpMatch(".?(Promise|Thenable)(Like)?")
  }

  private Node unwrapPromiseType(Node promiseType) {
    exists(GenericTypeExpr type |
      promiseType = type and
      isPromiseTypeName(type.getTypeAccess().(LocalTypeAccess).getName()) and
      result = type.getTypeArgument(0)
    )
    or
    exists(JSDocAppliedTypeExpr type |
      promiseType = type and
      isPromiseTypeName(type.getHead().(JSDocLocalTypeAccess).getName()) and
      result = type.getArgument(0)
    )
  }

  predicate contextualType(Node value, Node type) {
    exists(LocalVariableLike v |
      type = v.getADeclaration().getTypeAnnotation() and
      value = v.getAnAssignedExpr()
    )
    or
    exists(InvokeExpr call, Function target, int i |
      callTarget(call, target) and
      value = call.getArgument(i) and
      type = target.getParameter(i).getTypeAnnotation()
    )
    or
    exists(Function lambda, Node returnType |
      value = lambda.getAReturnedExpr() and
      functionReturnType(lambda, returnType)
    |
      not lambda.isAsyncOrGenerator() and
      type = returnType
      or
      lambda.isAsync() and
      type = unwrapPromiseType(returnType)
    )
    or
    exists(ObjectExpr object, Node objectType, Node host, string name |
      contextualType(object, objectType) and
      typeMemberHostReaches(host, objectType) and
      typeMember(host, any(DataFlow::Content c | c.asPropertyName() = name), type) and
      value = object.getPropertyByName(name).getInit()
    )
    or
    exists(ArrayExpr array, Node arrayType, Node host |
      contextualType(array, arrayType) and
      typeMemberHostReaches(host, arrayType) and
      typeMember(host, any(DataFlow::Content c | c.isUnknownArrayElement()), type) and
      value = array.getAnElement()
    )
    or
    // If the contextual type is 'T' and a concrete type argument for 'T' is known, use that type argument as the type.
    exists(TypeParameter typeParam |
      valueHasContextualTypeEqualToTypeParameter(value, typeParam) and
      valueHasContextualTypeWithArgument(value, typeParam, type)
    )
    or
    // When the contextual type is needed for deriving another type, collapse the type to all the known base types.
    // This ensures that type arguments corresponding to base types can be found after deriving the new type.
    needsDerivedContextualTypeInfo(value) and
    exists(Node midType |
      contextualType(value, midType) and
      type = getABaseTypeFromTypeRef(midType)
    )
  }

  /**
   * Holds if `value` has the given `type`.
   */
  predicate valueHasType(Node value, Node type) {
    value.(BindingPattern).getTypeAnnotation() = type
    or
    value.(TypeAssertion).getTypeAnnotation() = type
    or
    value.(SatisfiesExpr).getTypeAnnotation() = type
    or
    exists(VarDecl decl |
      // ValueFlow::step is restricted to variables with at most one assignment. Allow the type annotation
      // of a variable to propagate to its uses, even if the variable has multiple assignments.
      type = decl.getTypeAnnotation() and
      value = decl.getVariable().(LocalVariableLike).getAnAccess()
    )
    or
    exists(MemberDeclaration member |
      value.(ThisExpr).getBindingContainer() = member.getInit() and
      type = getMemberBase(member)
    )
    or
    exists(ClassDefinition cls |
      value = cls and
      type = cls.getVariable()
    )
    or
    exists(FunctionDeclStmt fun |
      value = fun and
      type = fun.getVariable()
    )
    or
    exists(Function target | callTarget(value, target) |
      type = target.getReturnTypeAnnotation()
      or
      exists(ClassDefinition cls |
        target = cls.getConstructor().getBody() and
        type = cls
      )
    )
    or
    // Contextual typing for parameters
    exists(Function lambda, Function functionType, int i |
      contextualType(lambda, trackUnderlyingFunctionType(functionType))
      or
      exists(InterfaceDefinition interface |
        contextualType(lambda, trackType(interface)) and
        functionType = interface.getACallSignature().getBody()
      )
    |
      value = lambda.getParameter(i) and
      not exists(value.(Parameter).getTypeAnnotation()) and
      type = functionType.getParameter(i).getTypeAnnotation()
    )
    or
    exists(Node mid | valueHasType(mid, type) | ValueFlow::step(mid, value))
    or
    exists(Node mid, Node midType, DataFlow::ContentSet contents, Node host |
      valueReadStep(mid, contents, value) and
      valueHasType(mid, midType) and
      typeMemberHostReaches(host, midType) and
      typeMember(host, contents.getAReadContent(), type)
    )
    or
    // If the type is 'T' and a concrete type argument for 'T' is known, use that type argument as the type.
    exists(TypeParameter typeParam |
      valueHasTypeEqualToTypeParameter(value, typeParam) and
      valueHasTypeWithArgument(value, typeParam, type)
    )
    or
    // When the type of 'value' is needed for deriving another type, associate 'value' with all the base types as well.
    // This ensures that type arguments corresponding to base types can be found after deriving the new type.
    needsDerivedTypeInfo(value) and
    exists(Node midType |
      valueHasType(value, midType) and
      type = getABaseTypeFromTypeRef(midType)
    )
  }

  /**
   * Holds if `type` contains a use of `typeParam` but does not contain its declaration.
   */
  private predicate typeHasFreeTypeParameter(AstNode type, TypeParameter typeParam) {
    type = typeParam.getLocalTypeName().getAnAccess()
    or
    typeHasFreeTypeParameter(type.getAChild(), typeParam) and
    not type.(TypeParameterized).getATypeParameter() = typeParam
  }

  /**
   * Holds if `value` has a type that is a direct reference to `typeParam`.
   */
  pragma[nomagic]
  private predicate valueHasTypeEqualToTypeParameter(Node value, TypeParameter typeParam) {
    valueHasType(value, getATypeParameterAccess(typeParam))
  }

  /**
   * Holds if `value` has a contextual type that is a direct reference to `typeParam`.
   */
  pragma[nomagic]
  private predicate valueHasContextualTypeEqualToTypeParameter(Node value, TypeParameter typeParam) {
    contextualType(value, getATypeParameterAccess(typeParam))
  }

  /** Holds if the type of `value` is was derived from `otherValue`. */
  private predicate typeDerivedFromType(Node value, Node otherValue) {
    valueReadStep(otherValue, _, value)
    or
    exists(InvokeExpr invoke |
      value = invoke and
      otherValue = invoke.getCallee()
    )
  }

  /** Holds if the type of `value` is derived from the contextual type of `otherValue`. */
  private predicate typeDerivedFromContextualType(Node value, Node otherValue) {
    exists(Function lambda |
      value = lambda.getAParameter() and
      otherValue = lambda
    )
  }

  /** Holds if the contextual type of `value` is derived from the type of `otherValue`. */
  private predicate contextualTypeDerivedFromType(Node value, Node otherValue) {
    exists(InvokeExpr invoke |
      value = invoke.getAnArgument() and
      otherValue = invoke.getCallee()
    )
  }

  /** Holds if the contextual type of `value` is derived from the contextual type of `otherValue`. */
  private predicate contextualTypeDerivedFromContextualType(Node value, Node otherValue) {
    exists(Function lambda |
      not exists(lambda.getReturnTypeAnnotation()) and
      value = lambda.getAReturnedExpr() and
      otherValue = lambda
    )
    or
    exists(ObjectExpr object |
      value = object.getAProperty().getInit() and
      otherValue = object
    )
    or
    exists(ArrayExpr array |
      value = array.getAnElement() and
      otherValue = array
    )
  }

  /**
   * Holds if `value` has a type containing an free reference to `typeParam`.
   */
  private predicate valueHasTypeWithFreeTypeParameter(Node value, TypeParameter typeParam) {
    exists(Node type |
      (valueHasType(value, type) or valueHasTypeWithArgument(value, _, type)) and
      typeHasFreeTypeParameter(type, typeParam)
    )
  }

  /**
   * Holds if `value` has a contextual type containing a free reference to `typeParam`.
   */
  private predicate valueHasContextualTypeWithFreeTypeParameter(Node value, TypeParameter typeParam) {
    exists(Node type |
      (contextualType(value, type) or valueHasContextualTypeWithArgument(value, _, type)) and
      typeHasFreeTypeParameter(type, typeParam)
    )
  }

  /** Holds if the type of `value` is used to derive the type of another value. */
  private predicate needsDerivedTypeInfo(Node value) {
    (typeDerivedFromType(_, value) or contextualTypeDerivedFromType(_, value))
  }

  /**
   * Holds if `value` has a type where `typeParam` is instantiated with `type`.
   *
   * Concretely this should hold when `valueHasType` gives a type containing a free type parameter.
   * This predicate then provides the values of the type parameters.
   */
  pragma[nomagic]
  private predicate valueHasTypeWithArgument(Node value, TypeParameter typeParam, Node type) {
    exists(TypeInstantiation instantiation |
      // Restrict this to cases where another type is derived from 'value' and therefore might need its type arguments
      needsDerivedTypeInfo(value) and
      valueHasType(value, trackTypeInstantiation(instantiation)) and
      type = getTypeArgumentForParameter(instantiation, typeParam)
    )
    or
    // Preserve type arguments after deriving a type from another type.
    // For example:
    //   The type of `x.f` was derived from `x`, and `x` has type `{f: T}`.
    //   Then `x.f` gets the type `T`. We thus want to propagate knowledge of `T` from the type of `x`.
    exists(Node mid |
      typeDerivedFromType(value, mid) and
      valueHasTypeWithArgument(mid, typeParam, type) and
      valueHasTypeWithFreeTypeParameter(value, typeParam) // restrict to relevant type parameters
    )
    or
    // Preserve type arguments after deriving a type from a contextual type.
    // For example:
    //   For a lambda expression `x => {}`, the type of `x` is derived from the contextual type
    //   of the lambda. Suppose the contextual type is `(p: T) => void`, then `x` has type `T`
    //   and we thus want to propagate knowledge of `T` from the contextual type of the lambda.
    exists(Node mid |
      typeDerivedFromContextualType(value, mid) and
      valueHasContextualTypeWithArgument(mid, typeParam, type) and
      valueHasTypeWithFreeTypeParameter(value, typeParam)
    )
    or
    exists(Node mid | valueHasTypeWithArgument(mid, typeParam, type) | ValueFlow::step(mid, value))
  }

  private predicate needsDerivedContextualTypeInfo(Node value) {
    (typeDerivedFromContextualType(_, value) or contextualTypeDerivedFromContextualType(_, value))
  }

  /**
   * Holds if `value` has a contextual type where `typeParam` is instantiated with `type`.
   */
  pragma[nomagic]
  private predicate valueHasContextualTypeWithArgument(
    Node value, TypeParameter typeParam, Node type
  ) {
    exists(TypeInstantiation instantiation |
      // Restrict this to cases where another type is derived from the contextual type of 'value' and therefore might need its type arguments
      needsDerivedContextualTypeInfo(value) and
      contextualType(value, trackTypeInstantiation(instantiation)) and
      type = getTypeArgumentForParameter(instantiation, typeParam)
    )
    or
    // Preserve type arguments after deriving a contextual type from a (non-contextual) type.
    // For example:
    //   For a call `f(e)`, the contextual type of `e` is derived from the type of `f`.
    exists(Node mid |
      contextualTypeDerivedFromType(value, mid) and
      valueHasTypeWithArgument(mid, typeParam, type) and
      valueHasContextualTypeWithFreeTypeParameter(value, typeParam)
    )
    or
    // Preserve type arguments after deriving a contextual type from a contextual type.
    // For example:
    //   For an array literal `[e]` the contextual type of `e` is derived from the contextual
    //   type of the array literal.
    exists(Node mid |
      contextualTypeDerivedFromContextualType(value, mid) and
      valueHasContextualTypeWithArgument(mid, typeParam, type) and
      valueHasContextualTypeWithFreeTypeParameter(value, typeParam)
    )
    or
    exists(Node mid | valueHasTypeWithArgument(mid, typeParam, type) | ValueFlow::step(mid, value))
  }

  private Node trackTypeParameterHost1(TypeParameterized host) {
    result = host and
    host.hasTypeParameters()
    or
    TypeFlow::step(trackTypeParameterHost1(host), result)
  }

  private Node trackTypeParameterHost(TypeParameterized host) {
    result = trackTypeParameterHost1(host)
    or
    result = trackClassValue(host)
  }

  private Node trackTypeInstantiation(TypeInstantiation instantiation) {
    result = instantiation
    or
    TypeFlow::step(trackTypeInstantiation(instantiation), result)
  }

  private Node getTypeArgumentForParameter(TypeInstantiation instantiation, TypeParameter param) {
    exists(TypeParameterized host, int i |
      trackTypeParameterHost(host) = instantiation.getHead() and
      param = host.getTypeParameter(i) and
      result = instantiation.getTypeArgument(i)
    )
  }

  abstract private class TypeInstantiationImpl extends Node {
    abstract Node getHead();

    abstract Node getTypeArgument(int n);
  }

  final private class TypeInstantiation = TypeInstantiationImpl;

  private class GenericTypeExprAsInstantiation extends TypeInstantiationImpl instanceof GenericTypeExpr
  {
    override Node getHead() { result = GenericTypeExpr.super.getTypeAccess() }

    override Node getTypeArgument(int n) { result = GenericTypeExpr.super.getTypeArgument(n) }
  }

  private class ExpressionWithTypeArgumentsAsInstantiation extends TypeInstantiationImpl instanceof ExpressionWithTypeArguments
  {
    override Node getHead() { result = ExpressionWithTypeArguments.super.getExpression() }

    override Node getTypeArgument(int n) {
      result = ExpressionWithTypeArguments.super.getTypeArgument(n)
    }
  }

  private class JSDocAppliedTypeAsInstantiation extends TypeInstantiationImpl instanceof JSDocAppliedTypeExpr
  {
    override Node getHead() { result = JSDocAppliedTypeExpr.super.getHead() }

    override Node getTypeArgument(int n) { result = JSDocAppliedTypeExpr.super.getArgument(n) }
  }

  /**
   * Holds if the type of `value` has the external type `<mod>.<name>` as an underlying type.
   */
  predicate valueHasUnderlyingType(Node value, string mod, string name) {
    exists(Node type |
      valueHasType(value, type) and
      UnderlyingTypes::nodeHasUnderlyingType(type, mod, name)
    )
    or
    exists(TypeParameter typeParam, Node underlyingType |
      valueHasUnderlyingTypeParameterType(value, typeParam) and
      valueHasTypeWithArgument(value, typeParam, underlyingType) and
      UnderlyingTypes::nodeHasUnderlyingType(underlyingType, mod, name)
    )
  }

  /**
   * Holds if the type of `value` has the the given class as an underlying type.
   */
  predicate valueHasUnderlyingClassType(Node value, DataFlow::ClassNode cls) {
    exists(Node type |
      valueHasType(value, type) and
      UnderlyingTypes::nodeHasUnderlyingClassType(type, cls)
    )
    or
    exists(TypeParameter typeParam, Node underlyingType |
      valueHasUnderlyingTypeParameterType(value, typeParam) and
      valueHasTypeWithArgument(value, typeParam, underlyingType) and
      UnderlyingTypes::nodeHasUnderlyingClassType(underlyingType, cls)
    )
  }

  /**
   * Holds if the type of `value` has `typeParam` as an underlying type.
   */
  private predicate valueHasUnderlyingTypeParameterType(Node value, TypeParameter typeParam) {
    exists(Node type | UnderlyingTypes::nodeHasUnderlyingTypeParameterType(type, typeParam) |
      valueHasType(value, type)
      or
      exists(TypeParameter midParam |
        valueHasUnderlyingTypeParameterType(value, midParam) and
        valueHasTypeWithArgument(value, midParam, type)
      )
    )
  }

  signature predicate nodeSig(Node node);

  /**
   * Tracks types that have a certain property, in the sense that:
   * - an intersection type has the property if any member has the property
   * - a union type has the property if all its members have the property
   */
  module TrackMustProp<nodeSig/1 directlyHasProperty> {
    predicate hasProperty(Node node) {
      directlyHasProperty(node)
      or
      exists(Node mid |
        hasProperty(mid) and
        TypeFlow::step(mid, node)
      )
      or
      unionHasProp(node)
      or
      hasProperty(node.(IntersectionTypeExpr).getAnElementType())
      or
      exists(ConditionalTypeExpr cond |
        node = cond and
        hasProperty(cond.getTrueType()) and
        hasProperty(cond.getFalseType())
      )
    }

    private predicate unionHasProp(UnionTypeExpr node, int n) {
      hasProperty(node.getElementType(0)) and n = 1
      or
      unionHasProp(node, n - 1) and
      hasProperty(node.getElementType(n - 1))
    }

    private predicate unionHasProp(UnionTypeExpr node) {
      unionHasProp(node, node.getNumElementType())
    }
  }

  module ValueHasProperty<nodeSig/1 typeHasProperty> {
    predicate valueHasProperty(Node value) {
      exists(Node type |
        valueHasType(value, type) and
        typeHasProperty(type)
      )
    }
  }

  private predicate isSanitizingPrimitiveTypeBase(Node node) {
    node.(TypeExpr).isNumbery()
    or
    node.(TypeExpr).isBooleany()
    or
    node.(TypeExpr).isNull()
    or
    node.(TypeExpr).isUndefined()
    or
    node.(TypeExpr).isVoid()
    or
    node.(TypeExpr).isNever()
    or
    node.(TypeExpr).isBigInt()
    or
    node.(TypeExpr).isSymbol()
    or
    node instanceof LiteralTypeExpr
    or
    node = any(EnumMember m).getIdentifier() // enum members are constant
    or
    node instanceof EnumDeclaration // enums are unions of constants
  }

  /**
   * Holds if `node` refers to a type that is considered untaintable (if actually enforced at runtime).
   *
   * Specifically, the types `number`, `boolean`, `null`, `undefined`, `void`, `never`, as well as literal types (`"foo"`)
   * and enums and enum members have this property.
   */
  predicate isSanitizingPrimitiveType =
    TrackMustProp<isSanitizingPrimitiveTypeBase/1>::hasProperty/1;

  /**
   * Holds if `value` has a type that is considered untaintable (if actually enforced at runtime).
   *
   * See `isSanitizingPrimitiveType`.
   */
  predicate valueHasSanitizingPrimitiveType =
    ValueHasProperty<isSanitizingPrimitiveType/1>::valueHasProperty/1;

  private predicate isPromiseBase(Node node) { exists(unwrapPromiseType(node)) }

  /**
   * Holds if the given type is a Promise object. Does not hold for unions unless all parts of the union are promises.
   */
  predicate isPromiseType = TrackMustProp<isPromiseBase/1>::hasProperty/1;

  /**
   * Holds if the given value has a type that implied it is a Promise object. Does not hold for unions unless all parts of the union are promises.
   */
  predicate valueHasPromiseType = ValueHasProperty<isPromiseType/1>::valueHasProperty/1;

  /**
   * Holds if `type` contains `string` or `any`, possibly wrapped in a promise.
   */
  predicate hasUnderlyingStringOrAnyType(Node type) {
    type.(TypeAnnotation).isStringy()
    or
    type.(TypeAnnotation).isAny()
    or
    type instanceof StringLiteralTypeExpr
    or
    type instanceof TemplateLiteralTypeExpr
    or
    exists(Node mid | hasUnderlyingStringOrAnyType(mid) |
      TypeFlow::step(mid, type)
      or
      UnderlyingTypes::underlyingTypeStep(mid, type)
      or
      type = unwrapPromiseType(mid)
    )
  }
}
