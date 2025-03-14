private import javascript

module TypeResolution {
  private class NodeBase =
    @expr or @typeexpr or @lexical_name or @toplevel or @class_decl_stmt or @namespace_definition;

  class Node extends NodeBase {
    string toString() {
      result = this.(AstNode).toString()
      or
      result = this.(LexicalName).toString()
    }

    Location getLocation() {
      result = this.(AstNode).getLocation()
      or
      result = this.(LocalVariable).getLocation()
    }
  }

  private class ModuleLike extends AstNode {
    ModuleLike() {
      this instanceof Module
      or
      this instanceof NamespaceDefinition
    }
  }

  predicate defUseStepCommon(Node node1, Node node2) {
    // Import paths are part of the graph and has an incoming edge from the imported module, if found.
    // This ensures we can also use the PathExpr as a source when working with external (unresolved) modules.
    exists(Import imprt |
      node1 = imprt.getImportedModule() and
      node2 = imprt.getImportedPath()
    )
    or
    exists(ImportNamespaceSpecifier spec |
      node1 = spec.getImportDeclaration().getImportedPath() and
      node2 = spec.getLocal()
    )
    or
    exists(ExportNamespaceSpecifier spec |
      node1 = spec.getExportDeclaration().(ReExportDeclaration).getImportedPath() and
      node2 = spec
    )
    or
    exists(ExportAssignDeclaration assign |
      node1 = assign.getExpression() and
      node2 = assign.getContainer()
    )
    or
    exists(ImportEqualsDeclaration imprt |
      node1 = imprt.getImportedEntity() and
      node2 = imprt.getIdentifier()
    )
    or
    exists(ExternalModuleReference ref |
      node1 = ref.getImportedPath() and
      node2 = ref
    )
    or
    exists(ImportTypeExpr imprt |
      node1 = imprt.getPathExpr() and // TODO: ImportTypeExpr does not seem to be resolved to a Module
      node2 = imprt
    )
    or
    exists(ClassOrInterface cls |
      node1 = cls and
      node2 = cls.getIdentifier()
    )
    or
    exists(NamespaceDefinition def |
      node1 = def and
      node2 = def.getIdentifier()
    )
    or
    exists(EnumMember def |
      node1 = def.getInitializer() and
      node2 = def.getIdentifier()
    )
    or
    exists(TypeAliasDeclaration alias |
      node1 = alias.getDefinition() and
      node2 = alias.getIdentifier()
    )
    or
    exists(ParenthesizedTypeExpr type |
      node1 = type.getElementType() and
      node2 = type
    )
    or
    exists(ParenthesisExpr expr |
      node1 = expr.getExpression() and
      node2 = expr
    )
  }

  private predicate readStepCommon(Node node1, string name, Node node2) {
    exists(QualifiedTypeAccess access |
      node1 = access.getQualifier() and
      name = access.getIdentifier().getName() and
      node2 = access
    )
    or
    exists(QualifiedNamespaceAccess access |
      node1 = access.getQualifier() and
      name = access.getIdentifier().getName() and
      node2 = access
    )
    or
    exists(PropAccess access |
      node1 = access.getBase() and
      name = access.getPropertyName() and
      node2 = access
    )
    or
    exists(ImportSpecifier spec |
      node1 = spec.getImportDeclaration().getImportedPath() and
      name = spec.getImportedName() and
      node2 = spec.getLocal()
    )
  }

  signature module TypeResolutionInputSig {
    predicate isRelevantVariable(LexicalName name);
  }

  module TypeResolutionValueAndNamespace implements TypeResolutionInputSig {
    predicate isRelevantVariable(LexicalName name) {
      name instanceof LocalVariable
      or
      name instanceof LocalNamespaceName
    }
  }

  module TypeResolutionTypes implements TypeResolutionInputSig {
    predicate isRelevantVariable(LexicalName name) { name instanceof LocalTypeName }
  }

  module ValueFlow = TypeRes<TypeResolutionValueAndNamespace>;

  module TypeFlow = TypeRes<TypeResolutionTypes>;

  module TypeRes<TypeResolutionInputSig S> {
    Node getModuleExport(ModuleLike mod, string name) {
      exists(ExportDeclaration exprt |
        mod = exprt.getContainer() and
        exprt.exportsAs(result, name) and
        S::isRelevantVariable(result)
      )
      or
      exists(ExportNamespaceSpecifier spec |
        result = spec and
        mod = spec.getContainer() and
        name = spec.getExportedName()
      )
      or
      exists(EnumDeclaration enum |
        mod = enum and
        result = enum.getMemberByName(name).getIdentifier()
      )
    }

    predicate defUseStepSpecific(Node node1, Node node2) {
      exists(LexicalName name | S::isRelevantVariable(name) |
        node1.(LexicalDecl).getALexicalName() = name and
        node2 = name
        or
        node1 = name and
        node2.(LexicalAccess).getALexicalName() = name
      )
      or
      exists(Node base, string name, ModuleLike mod |
        readStepCommon(base, name, node2) and
        base = trackModule(mod) and
        node1 = getModuleExport(mod, name)
      )
    }

    pragma[inline]
    predicate defUseStep(Node node1, Node node2) {
      defUseStepCommon(node1, node2)
      or
      defUseStepSpecific(node1, node2)
    }

    signature predicate nodeSig(Node node);

    module Track<nodeSig/1 isSource> {
      Node track(Node source) {
        isSource(source) and
        result = source
        or
        defUseStep(track(source), result)
      }
    }

    signature class AstNodeSig extends AstNode;

    module TrackNode<AstNodeSig Source> {
      Node track(Source source) {
        result = source
        or
        defUseStep(track(source), result)
      }
    }
  }

  predicate trackModule = ValueFlow::TrackNode<ModuleLike>::track/1;

  predicate trackClassValue = ValueFlow::TrackNode<ClassDefinition>::track/1;

  predicate trackType = TypeFlow::TrackNode<TypeDefinition>::track/1;

  bindingset[moduleName]
  private predicate isExternalModuleName(string moduleName) {
    not moduleName.regexpMatch("^(\\.|/).*")
  }

  bindingset[name]
  private string normalizeModuleName(string name) {
    result =
      name.regexpReplaceAll("^node:", "")
          .regexpReplaceAll("\\.[jt]sx?$", "")
          .regexpReplaceAll("/(index)?$", "")
  }

  /**
   * Holds if `node` is a reference to the given module, or a qualified name rooted in that module.
   *
   * If `qualifiedName` is empty, `node` refers to the module itself.
   *
   * If `mod` is the string `"global"`, `node` refers to a global access path.
   */
  predicate nodeRefersToModule(Node node, string mod, string qualifiedName) {
    exists(Import imprt |
      node = imprt.getImportedPath() and
      mod = normalizeModuleName(imprt.getImportedPath().getValue()) and
      isExternalModuleName(mod) and
      qualifiedName = ""
    )
    or
    mod = "global" and
    exists(LocalNamespaceAccess access |
      node = access and
      not exists(access.getLocalNamespaceName()) and
      access.getName() = qualifiedName
    )
    or
    // Additionally track through bulk re-exports (`export * from 'mod`).
    // These are normally handled by 'exportAs' which supports various shadowing rules,
    // but has no effect when the ultimate re-exported module is not resolved to a Module.
    // We propagate external module refs through bulk re-exports and ignore shadowing rules.
    exists(BulkReExportDeclaration reExport |
      nodeRefersToModule(reExport.getImportedPath(), mod, qualifiedName) and
      node = reExport.getContainer()
    )
    or
    exists(Node mid |
      nodeRefersToModule(mid, mod, qualifiedName) and
      ValueFlow::defUseStep(mid, node) and
      not node instanceof Variable // avoid a lot of unnecessary tuples
    )
    or
    exists(Node mid, string prefix, string step |
      nodeRefersToModule(mid, mod, prefix) and
      readStepCommon(mid, step, node) and
      qualifiedName = append(prefix, step)
    )
  }

  predicate underlyingTypeStep(Node node1, Node node2) {
    exists(ClassOrInterface cls |
      (
        node1 = cls.getSuperClass() or
        node1 = cls.getASuperInterface()
      ) and
      node2 = cls
    )
    or
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
  }

  bindingset[a, b]
  private string append(string a, string b) {
    if b = "default"
    then result = a
    else (
      (if a = "" or b = "" then result = a + b else result = a + "." + b) and
      result.length() < 100
    )
  }

  predicate nodeHasUnderlyingType(Node node, string mod, string name) {
    exists(Node mid, string prefix, string step |
      nodeRefersToModule(mid, mod, prefix) and
      readStepCommon(mid, step, node) and
      name = append(prefix, step)
    )
    or
    exists(Node mid | nodeHasUnderlyingType(mid, mod, name) |
      TypeFlow::defUseStep(mid, node)
      or
      underlyingTypeStep(mid, node)
    )
  }

  predicate nodeHasUnderlyingType2(TypeExpr node, string mod, string name) {
    nodeHasUnderlyingType(node, mod, name)
  }

  cached
  string getStringValue(Node node) {
    result = node.(Expr).getStringValue()
    or
    result = node.(Label).getName()
    or
    exists(Node mid |
      result = getStringValue(mid) and
      ValueFlow::defUseStep(mid, node) and
      // Exclude steps where we use the import path as representative for the imported module
      not mid = any(Import imprt).getImportedPath()
    )
  }

  cached
  int getIntValue(Node node) {
    result = node.(Expr).getIntValue()
    or
    exists(Node mid |
      result = getIntValue(mid) and
      ValueFlow::defUseStep(mid, node)
    )
  }

  string getStringValueTest(Node node) {
    result = getStringValue(node) and
    not exists(node.(Expr).getStringValue())
  }

  /**
   * Holds if `node` refers to the type `number`, `boolean`, `null`, `undefined`, `void`, `never`
   * or some combination thereof.
   */
  predicate isSanitizingPrimitiveType(Node node) {
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
    isSanitizingPrimitiveTypeUnion(node)
    or
    isSanitizingPrimitiveType(node.(IntersectionTypeExpr).getAnElementType())
    or
    exists(Node mid |
      isSanitizingPrimitiveType(mid) and
      TypeFlow::defUseStep(mid, node)
    )
  }

  private predicate isSanitizingPrimitiveTypeUnion(UnionTypeExpr node, int n) {
    isSanitizingPrimitiveType(node.getElementType(0)) and n = 1
    or
    isSanitizingPrimitiveTypeUnion(node, n - 1) and
    isSanitizingPrimitiveType(node.getElementType(n - 1))
  }

  private predicate isSanitizingPrimitiveTypeUnion(UnionTypeExpr node) {
    isSanitizingPrimitiveTypeUnion(node, node.getNumElementType())
  }
}
