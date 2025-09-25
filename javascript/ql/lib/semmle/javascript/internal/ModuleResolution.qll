private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps

pragma[nomagic]
private GlobalVarAccess globalAccess(Module mod, string name) {
  result.getName() = name and
  result.getTopLevel() = mod and
  name = ["exports", "module"] // manually restrict size of predicate
}

private DataFlow::SourceNode moduleObjectRef(Module mod) {
  result = DataFlow::ssaDefinitionNode(Ssa::implicitInit(mod.getScope().getVariable("module")))
  or
  result = globalAccess(mod, "module").flow()
}

DataFlow::Node exportsRhs(Module mod) {
  result = moduleObjectRef(mod).getAPropertyWrite("exports").getRhs()
  or
  result = mod.(AmdModule).getDefine().getFactoryFunction().getAReturnedExpr().flow()
  or
  result = mod.(Closure::ClosureModule).getExportsVariable().getAnAssignedValue().flow()
  or
  exists(ExportDefaultDeclaration exprt |
    // In Closure modules, 'export default' is treated as setting the whole exports object
    mod instanceof Closure::ClosureModule and
    exprt.getContainer() = mod and
    result = DataFlow::valueNode(exprt.getOperand())
  )
  or
  exists(ExportAssignDeclaration exprt |
    mod = exprt.getContainer() and
    result = exprt.getExpression().flow()
  )
}

DataFlow::SourceNode initialExportsVar(Module mod) {
  result = DataFlow::ssaDefinitionNode(Ssa::implicitInit(mod.getScope().getVariable("exports")))
}

DataFlow::SourceNode exportsRef(Module mod) {
  result = initialExportsVar(mod)
  or
  result = moduleObjectRef(mod).getAPropertyRead("exports")
  or
  result = globalAccess(mod, "exports").flow()
  or
  result = mod.(AmdModule).getDefine().getExportsParameter().flow()
  or
  result = exportsRhs(mod).getALocalSource()
}

/** Holds if `node` is stored into `module.exports.<name>` within the given module. */
private predicate storeToExports(DataFlow::Node value, Module mod, string name) {
  value = exportsRef(mod).getAPropertyWrite(name).getRhs()
  or
  exists(ExportDeclaration decl, Variable v |
    decl.exportsAs(v, name) and
    decl.getContainer() = mod
  |
    value = v.getAnAssignedValue().flow()
    or
    // Workaround for destructuring patterns where there the VarRef node is
    // currently disconnected from the data flow graph. Use the TPropNode instead.
    exists(PropertyPattern p |
      p.getValuePattern() = v.getAReference() and
      value = TPropNode(p)
    )
  )
  or
  exists(ExportDefaultDeclaration decl |
    mod = decl.getContainer() and
    not mod instanceof Closure::ClosureModule and
    name = "default" and
    value = DataFlow::valueNode(decl.getOperand())
  )
  or
  exists(ExportSpecifier spec |
    value = DataFlow::valueNode(spec) and
    name = spec.getExportedName() and
    mod = spec.getContainer() and
    spec.getExportDeclaration() instanceof ReExportDeclaration
  )
}

predicate storeStep(DataFlow::Node node1, string prop, DataFlow::SourceNode node2) {
  exists(Module mod |
    storeToExports(node1, mod, prop) and
    node2 = TExportNode(mod.getFile())
  )
  or
  node1 = node2.getAPropertyWrite(prop).getRhs() and
  not node2 = exportsRef(_) // redirected to TExportNode
  or
  exists(NamespaceDeclaration namespace, ExportDeclaration exprt, Variable v |
    exprt.exportsAs(v, prop) and
    exprt.getContainer() = namespace and
    node1 = v.getAnAssignedValue().flow() and
    node2 = DataFlow::valueNode(namespace)
  )
}

predicate valueBigStep(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
  exists(Import imprt |
    node1 = TExportNode(imprt.getImportedFile()) and
    node2 = imprt.getImportedModuleNodeStrict()
  )
  or
  node1.flowsTo(node2) and
  node1 != node2
  or
  exists(Module mod |
    node1 = exportsRhs(mod).getALocalSource() and
    node2 = TExportNode(mod.getFile())
    or
    node1 = TExportNode(mod.getFile()) and
    node2 = exportsRef(mod)
  )
  or
  exists(ExportNamespaceSpecifier spec |
    node1 =
      TExportNode(spec.getExportDeclaration().(ReExportDeclaration).getReExportedModule().getFile()) and
    node2 = DataFlow::valueNode(spec)
  )
  or
  exists(DataFlow::SourceNode obj |
    node1 = obj and
    node2 = obj.getAPropertySource().(DataFlow::FunctionNode).getReceiver()
  )
}

predicate readStep(DataFlow::SourceNode node1, string prop, DataFlow::SourceNode node2) {
  node2 = node1.getAPropertyRead(prop)
  or
  exists(NamedExportSpecifier spec |
    node1 =
      TExportNode(spec.getExportDeclaration().(ReExportDeclaration).getReExportedModule().getFile()) and
    prop = spec.getLocalName() and
    node2 = DataFlow::valueNode(spec)
  )
}

private predicate shouldFindRootValue(DataFlow::SourceNode node) {
  not node instanceof DataFlow::GlobalVarRefNode and
  (
    storeStep(track(_).getALocalUse(), _, node)
    or
    storeStep(any(DataFlow::InvokeNode n).getALocalUse(), _, node)
    or
    exists(DataFlow::SourceNode next | shouldFindRootValue(next) |
      valueBigStep(node, next) or
      readStep(node, _, next) or
      storeReadStep(node.getALocalUse(), next)
    )
  )
}

pragma[nomagic]
private predicate shouldTrack(DataFlow::SourceNode node) {
  node instanceof DataFlow::FunctionNode
  or
  node instanceof DataFlow::ClassNode
  or
  node instanceof DataFlow::ExportNode
  or
  shouldFindRootValue(node) and
  not valueBigStep(_, node)
}

pragma[nomagic]
DataFlow::SourceNode track(DataFlow::SourceNode node) {
  shouldTrack(node) and
  result = node
  or
  valueBigStep(track(node), result)
  or
  storeReadStep(track(node).getALocalUse(), result)
}

pragma[nomagic]
private predicate deepStore(DataFlow::SourceNode object, string prop, DataFlow::Node value) {
  storeStep(value, prop, track(object))
}

pragma[nomagic]
private predicate deepRead(DataFlow::SourceNode object, string prop, DataFlow::SourceNode value) {
  readStep(track(object), prop, value)
}

pragma[nomagic]
predicate storeReadStep(DataFlow::Node node1, DataFlow::SourceNode node2) {
  exists(DataFlow::SourceNode object, string prop |
    deepStore(object, prop, node1) and
    deepRead(object, prop, node2)
  )
}

predicate moduleResolutionStep(DataFlow::Node node1, DataFlow::Node node2) {
  storeReadStep(node1, node2)
  or
  exists(Import imprt |
    node1 = TExportNode(imprt.getImportedFile()) and
    node2 = imprt.getImportedModuleNodeStrict()
  )
  or
  exists(Module mod |
    node1 = exportsRhs(mod).getALocalSource() and
    node2 = TExportNode(mod.getFile())
    or
    node1 = TExportNode(mod.getFile()) and
    node2 = exportsRef(mod)
  )
}

module Debug {
  private predicate baseline(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
    FlowSteps::propertyFlowStep(node1.getALocalUse(), node2)
  }

  pragma[nomagic]
  predicate current1(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
    valueBigStep(node1, node2)
    or
    storeReadStep(node1.getALocalUse(), node2)
  }

  predicate current(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
    current1(node1, node2) and not node1 instanceof TExportNode
    or
    exists(Module mod |
      current1(TExportNode(mod.getFile()), node2) and
      node1 = exportsRef(mod)
    )
  }

  pragma[nomagic]
  query predicate lostStep(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
    baseline(node1, node2) and
    not current(node1, node2) and
    not node1.getTopLevel().isExterns() and
    not node2.getTopLevel().isExterns()
  }

  pragma[nomagic]
  query predicate gainedStep(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
    not baseline(node1, node2) and
    current(node1, node2) and
    not node1.getTopLevel().isExterns() and
    not node2.getTopLevel().isExterns()
  }
}
