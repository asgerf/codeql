private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import semmle.javascript.GlobalAccessPaths

pragma[nomagic]
private GlobalVarAccess globalAccess(Module mod, string name) {
  result.getName() = name and
  result.getTopLevel() = mod and
  name = ["exports", "module"] // manually restrict size of predicate
}

private DataFlow::SourceNode moduleObjectRef(Module mod) {
  result = DataFlow::ssaDefinitionNode(Ssa::implicitInit(mod.getScope().getVariable("module")))
  or
  result = mod.(AmdModule).getDefine().getModuleParameter().flow()
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
  or
  exists(DataFlow::ClassNode cls |
    node1 = cls.getInstanceMethod(prop) and
    node2 = getCanonicalInstanceNode(cls)
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
    node2 = obj.getAPropertySource().(DataFlow::FunctionNode).getReceiver() and
    // Do not propagate namespaces into 'this' in a constructor
    not node2 = any(DataFlow::ClassNode cls).getConstructor().getReceiver()
  )
  or
  // We don't step into calls in this stage, except for immediately-invoked function expressions (handled by `flowsTo`).
  // Similarly, also handle function expressions that are immediately used in a partial invocation. This is often needed
  // for code of form `function() { ... }.bind(this)` from before arrow functions existed in JS.
  exists(
    DataFlow::PartialInvokeNode partial, DataFlow::FunctionNode callback, DataFlow::Node argument
  |
    node1 = argument.getALocalSource()
  |
    exists(int index |
      partial.isPartialArgument(callback, argument, index) and
      node2 = callback.getParameter(index)
    )
    or
    argument = partial.getBoundReceiver(callback) and
    node2 = callback.getReceiver()
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

private DataFlow::SourceNode getCanonicalInstanceNode(DataFlow::ClassNode cls) {
  result = cls.getConstructor().getReceiver()
}

pragma[nomagic]
private predicate shouldTrack(DataFlow::SourceNode node) {
  node instanceof DataFlow::FunctionNode
  or
  node instanceof DataFlow::ClassNode
  or
  node = getCanonicalInstanceNode(_)
  or
  node instanceof DataFlow::ExportNode
  or
  shouldFindRootValue(node) and
  not valueBigStep(_, node)
  or
  exists(node)
}

// private predicate shouldNotTrack(DataFlow::SourceNode node) { not shouldTrack(node) }
pragma[inline]
private predicate bigStep(
  DataFlow::SourceNode trackedValue, DataFlow::SourceNode node1, DataFlow::SourceNode node2
) {
  valueBigStep(node1, node2)
  or
  storeReadStep(node1.getALocalUse(), node2)
  or
  AccessPath::step(node1.getALocalUse(), node2)
  or
  constructorCloneStep(node1, node2) and
  allowConstructorCloneStep(trackedValue)
}

pragma[nomagic]
DataFlow::SourceNode track(DataFlow::SourceNode node) {
  shouldTrack(node) and
  result = node
  or
  bigStep(node, track(node), result)
}

pragma[nomagic]
DataFlow::SourceNode trackOut(DataFlow::SourceNode node) {
  returnStep(track(node), result)
  or
  returnStep(trackOut(node), result)
  or
  bigStep(node, trackOut(node), result)
}

pragma[nomagic]
DataFlow::SourceNode trackOutThenIn(DataFlow::SourceNode node) {
  argumentPassingStep(trackOut(node), result)
  or
  argumentPassingStep(trackOutThenIn(node), result)
  or
  bigStep(node, trackOutThenIn(node), result)
}

pragma[nomagic]
DataFlow::SourceNode trackIn(DataFlow::SourceNode node) {
  argumentPassingStep(track(node), result)
  or
  argumentPassingStep(trackIn(node), result)
  or
  bigStep(node, trackIn(node), result)
}

pragma[inline]
DataFlow::SourceNode trackAny(DataFlow::SourceNode node) {
  result = [track(node), trackOut(node), trackOutThenIn(node), trackIn(node)]
}

private predicate viableCallable(DataFlow::InvokeNode call, DataFlow::FunctionNode target) {
  call = [track(target), trackOut(target)].getAnInvocation()
  or
  exists(DataFlow::ClassNode cls |
    call = [track(cls), trackOut(cls)].getAnInvocation() and
    target = cls.getConstructor()
  )
}

private predicate returnStep(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
  exists(DataFlow::InvokeNode call, DataFlow::FunctionNode target | viableCallable(call, target) |
    node1 = target.getReturnNode().getALocalSource() and
    node2 = call
  )
}

private DataFlow::SourceNode getReceiverToPropagate(DataFlow::InvokeNode call) {
  call.asExpr() instanceof SuperCall and
  result = DataFlow::thisNode(call.getEnclosingFunction().getThisBinder())
  or
  call instanceof DataFlow::NewNode and
  result = call
  or
  // Do not propagate the receiver of method calls, as it is too tightly coupled to method dispatch,
  // leading to rampant spurious flow of 'this'.
  // It is however safe for call where the callee does not immediately depend on `this`, such as `f.call(this)`.
  result = call.(DataFlow::CallNode).getReceiver().getALocalSource() and
  not call.getCalleeNode() = result.getAPropertyRead()
}

private predicate argumentPassingStep(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
  exists(DataFlow::InvokeNode call, DataFlow::FunctionNode target | viableCallable(call, target) |
    exists(int i |
      node1 = call.getArgument(i).getALocalSource() and
      node2 = target.getParameter(i)
    )
    or
    node1 = getReceiverToPropagate(call) and
    node2 = target.getReceiver()
  )
}

private predicate constructorCloneStep(DataFlow::SourceNode node1, DataFlow::SourceNode node2) {
  node2 = node1.getAPropertyRead("constructor").getAnInstantiation()
}

private predicate allowConstructorCloneStep(DataFlow::SourceNode node) {
  node = any(DataFlow::ClassNode cls).getConstructor().getReceiver()
}

pragma[nomagic]
private predicate deepStoreNoReturn(DataFlow::SourceNode object, string prop, DataFlow::Node value) {
  (
    storeStep(value, prop, track(object))
    or
    storeStep(value, prop, trackIn(object))
  ) and
  not prop = "constructor" // avoid complications with 'constructor' assignments for now
}

// pragma[nomagic]
// private predicate deepStoreReturn(DataFlow::SourceNode object, string prop, DataFlow::Node value) {
//   storeStep(value, prop, trackOut(object))
//   or
//   storeStep(value, prop, trackOutThenIn(object))
// }
pragma[nomagic]
private predicate deepReadNoReturn(
  DataFlow::SourceNode object, string prop, DataFlow::SourceNode value
) {
  readStep(track(object), prop, value)
  or
  readStep(trackIn(object), prop, value)
}

pragma[nomagic]
private predicate deepReadReturn(
  DataFlow::SourceNode object, string prop, DataFlow::SourceNode value
) {
  readStep(trackOut(object), prop, value)
  or
  readStep(trackOutThenIn(object), prop, value)
}

pragma[nomagic]
private predicate globalStore(File file, GlobalVariable globalVar, DataFlow::Node value) {
  exists(AST::ValueNode rhs |
    rhs = globalVar.getAnAssignedValue() and
    file = rhs.getFile() and
    value = rhs.flow()
  )
}

pragma[nomagic]
private predicate globalRead(File file, GlobalVariable globalVar, DataFlow::SourceNode value) {
  exists(VarAccess access |
    access = globalVar.getAnAccess() and
    file = access.getFile() and
    value = access.flow()
  )
}

pragma[nomagic]
predicate storeReadStep(DataFlow::Node node1, DataFlow::SourceNode node2) {
  exists(DataFlow::SourceNode object, string prop |
    deepStoreNoReturn(object, prop, node1) and
    deepReadNoReturn(object, prop, node2)
    or
    deepStoreNoReturn(object, prop, node1) and
    deepReadReturn(object, prop, node2)
    // or
    // Note: this step is a little dubious?
    // deepStoreReturn(object, prop, node1) and
    // deepReadNoReturn(object, prop, node2)
  )
  or
  exists(File file, GlobalVariable v |
    globalStore(file, v, node1) and
    globalRead(file, v, node2)
  )
  or
  exists(DataFlow::ClassNode cls |
    node1 = getCanonicalInstanceNode(cls) and
    (
      deepReadNoReturn(cls, "prototype", node2)
      or
      deepReadReturn(cls, "prototype", node2)
    )
    or
    deepStoreNoReturn(cls, "prototype", node1) and
    node2 = getCanonicalInstanceNode(cls)
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
