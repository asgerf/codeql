import javascript
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import semmle.javascript.dataflow.internal.StepSummary
private import semmle.javascript.dataflow.TypeTracking
private import internal.CachedStages
private import semmle.javascript.dataflow.internal.DataFlowNode

module Deep {
  private predicate shouldTrack(DataFlow::SourceNode node) {
    not node.getTopLevel().isExterns() and
    not node.getAstNode().isAmbient() and
    not node.getFile().getBaseName().matches("%.d.ts") and
    // TODO: maybe don't track 'undefined' around?
    // only track synthetic return node of async/generator functions, where it represents an allocation
    not exists(Function f |
      DataFlow::functionReturnNode(node, f) and
      not f.isAsyncOrGenerator()
    )
  }

  private predicate initialState(DataFlow::SourceNode node, boolean hasCall, boolean hasReturn) {
    shouldTrack(node) and
    hasReturn = false and
    if node instanceof DataFlow::ParameterNode then hasCall = true else hasCall = false
  }

  pragma[nomagic]
  private predicate levelStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    StepSummary::step(pred, succ, LevelStep())
    or
    any(API::AdditionalUseStep st).step(pred, succ)
    or
    // additional flow `exports` or `module.exports` in `require('m')`
    exists(Import imp | imp.getImportedModuleNode() = succ |
      pred = DataFlow::exportsVarNode(imp.getImportedModule())
      or
      pred = DataFlow::moduleVarNode(imp.getImportedModule()).getAPropertyRead("exports")
    )
  }

  /**
   * Holds if `pred` is cloned or has its properties copied into `succ`.
   */
  pragma[nomagic]
  private predicate massAssignmentStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    // p -> { ...p }
    exists(ObjectExpr obj |
      succ = obj.flow() and
      pred =
        obj.getAProperty()
            .(SpreadProperty)
            .getInit()
            .(SpreadElement)
            .getOperand()
            .flow()
            .getALocalSource()
    )
  }

  pragma[nomagic]
  private predicate storeStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ, string prop) {
    StepSummary::step(pred, succ, StoreStep(prop))
  }

  pragma[nomagic]
  private predicate loadStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ, string prop) {
    StepSummary::step(pred, succ, LoadStep(prop))
  }

  pragma[nomagic]
  private predicate returnStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    StepSummary::step(pred, succ, ReturnStep())
  }

  pragma[nomagic]
  private predicate callStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    StepSummary::step(pred, succ, CallStep())
  }

  pragma[nomagic]
  private predicate loadStoreStep(
    DataFlow::SourceNode pred, DataFlow::SourceNode succ, string prop1, string prop2
  ) {
    StepSummary::step(pred, succ, LoadStoreStep(prop1, prop2))
    or
    StepSummary::step(pred, succ, CopyStep(prop1)) and prop2 = prop1
  }

  /**
   * Holds if `pred` can flow to `succ`.
   *
   * `hasCall` and `hasReturn` indicate if the path contains calls and returns, respectively.
   */
  pragma[nomagic]
  cached
  DataFlow::SourceNode trackNode(DataFlow::SourceNode node, boolean hasCall, boolean hasReturn) {
    initialState(node, hasCall, hasReturn) and
    result = node
    or
    exists(DataFlow::SourceNode mid |
      mid = trackNode(node, _, hasReturn) and
      callStep(mid, result) and
      hasCall = true
    )
    or
    exists(DataFlow::SourceNode mid |
      mid = trackNode(node, false, _) and
      returnStep(mid, result) and
      hasReturn = true and
      hasCall = false
    )
    or
    levelStep(trackNode(node, hasCall, hasReturn), result)
    or
    // note: for now, mass assignment steps are simply treated as level steps
    massAssignmentStep(trackNode(node, hasCall, hasReturn), result)
    or
    exists(boolean call1, boolean call2, boolean return1, boolean return2 |
      derivedPropStep(trackNode(node, call1, return1), result, call2, return2) and
      call1.booleanAnd(return2) = false and
      hasCall = call1.booleanOr(call2) and
      hasReturn = return1.booleanOr(return2)
    )
  }

  pragma[nomagic]
  private predicate boundInvocationStep(
    DataFlow::SourceNode pred, DataFlow::SourceNode succ, boolean promisified, int boundArgs
  ) {
    exists(Promisify::PromisifyCall promisify |
      pred = promisify.getArgument(0).getALocalSource() and
      succ = promisify and
      promisified = true and
      boundArgs = 0
    )
    or
    exists(DataFlow::PartialInvokeNode partial |
      succ = partial.getBoundFunction(pred.getALocalUse(), boundArgs) and
      promisified = false
    )
  }

  private DataFlow::SourceNode getABoundUse(
    DataFlow::SourceNode source, boolean hasCall, boolean hasReturn, boolean promisified,
    int boundArgs
  ) {
    boundInvocationStep(trackNode(source, hasCall, hasReturn), result, promisified, boundArgs)
    or
    exists(
      DataFlow::SourceNode mid, boolean call1, boolean return1, boolean promisified1,
      int boundArgs1, boolean call2, boolean return2, boolean promisified2, int boundArgs2
    |
      mid = getABoundUse(source, call1, return1, promisified1, boundArgs1) and
      boundInvocationStep(trackNode(mid, call2, return2), result, promisified2, boundArgs2) and
      promisified = promisified1.booleanOr(promisified2) and
      boundArgs = boundArgs1 + boundArgs2 and
      boundArgs in [0 .. 10] and
      call1.booleanAnd(return2) = false and
      hasCall = call1.booleanOr(call2) and
      hasReturn = return1.booleanOr(return2)
    )
  }

  /**
   * Gets a source node referring to a bound version of `originalCallee`.
   */
  DataFlow::SourceNode getABoundUseSite(
    DataFlow::SourceNode originalCallee, boolean promisified, int boundArgs
  ) {
    exists(boolean call1, boolean return1, boolean call2, boolean return2 |
      result =
        trackNode(getABoundUse(originalCallee, call1, return1, promisified, boundArgs), call2,
          return2) and
      call1.booleanAnd(return2) = false
    )
  }

  /**
   * Gets an invocation of `originalCallee` that has been through one or more promisification and/or argument-binding steps.
   */
  DataFlow::CallNode getABoundInvocation(
    DataFlow::SourceNode originalCallee, boolean promisified, int boundArgs
  ) {
    result = getABoundUseSite(originalCallee, promisified, boundArgs).getACall()
  }

  /**
   * Holds if `pred` can flow to `succ` via a store/load pair.
   *
   * `hasCall` and `hasReturn` indicate if the path of the carrying object contains
   * calls and returns, respectively.
   */
  pragma[nomagic]
  private predicate derivedPropStep(
    DataFlow::SourceNode pred, DataFlow::SourceNode succ, boolean hasCall, boolean hasReturn
  ) {
    exists(DataFlow::SourceNode obj, string prop |
      storeStep(pred, obj, prop) and
      loadStep(trackNode(obj, hasCall, hasReturn), succ, prop)
      or
      exists(boolean return1, boolean call1, boolean return2, boolean call2 |
        storeStep(pred, obj, prop) and
        indirectLoad(trackNode(obj, call1, return1), succ, call2, return2, prop) and
        call1.booleanAnd(return2) = false and
        hasCall = call1.booleanOr(call2) and
        hasReturn = return1.booleanOr(return2)
      )
    )
  }

  /**
   * Holds if the `prop` property of `pred` can flow to `succ` via one or more load-store steps
   * followed by a load step.
   *
   * `hasCall` and `hasReturn` indicate if the paths of the carrying objects contain
   * calls and returns, respectively.
   */
  pragma[nomagic]
  predicate indirectLoad(
    DataFlow::SourceNode pred, DataFlow::SourceNode succ, boolean hasCall, boolean hasReturn,
    string prop
  ) {
    exists(DataFlow::SourceNode mid, string midProp |
      loadStoreStep(pred, mid, prop, midProp) and
      loadStep(trackNode(mid, hasCall, hasReturn), succ, midProp)
      or
      exists(boolean call1, boolean return1, boolean call2, boolean return2 |
        loadStoreStep(pred, mid, prop, midProp) and
        indirectLoad(trackNode(mid, call1, return1), succ, call2, return2, prop) and
        call1.booleanAnd(return2) = false and
        hasCall = call1.booleanOr(call2) and
        hasReturn = return1.booleanOr(return2)
      )
    )
  }

  pragma[inline]
  DataFlow::SourceNode getLoad(DataFlow::SourceNode base, string prop) {
    exists(DataFlow::SourceNode ref, boolean call1, boolean return1 |
      ref = trackNode(base, call1, return1)
    |
      loadStep(ref, result, prop)
      or
      exists(boolean call2, boolean return2 |
        indirectLoad(ref, result, call2, return2, prop) and
        call1.booleanAnd(return2) = false
      )
    )
  }

  cached
  predicate hasFlowTo(DataFlow::SourceNode source, DataFlow::SourceNode dest) {
    trackNode(source, _, _) = dest
  }

  class Node extends TNode instanceof DataFlow::SourceNode {
    string toString() { result = this.(DataFlow::SourceNode).toString() }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.(DataFlow::SourceNode)
          .hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    cached
    DataFlow::SourceNode getAUse() { hasFlowTo(this, result) }

    cached
    DataFlow::SourceNode getASource() { hasFlowTo(result, this) }

    Node getAPropertyRead(string prop) { result = this.getAUse().getAPropertyRead(prop) }

    Node getAPropertyRead() { result = this.getAUse().getAPropertyRead() }

    DataFlow::PropWrite getAPropertyWrite(string name) {
      result = this.getAUse().getAPropertyWrite(name)
    }

    DataFlow::PropWrite getAPropertyWrite() { result = this.getAUse().getAPropertyWrite() }

    DataFlow::MethodCallNode getAMethodCall(string name) {
      result = this.getAUse().getAMethodCall(name)
    }

    DataFlow::MethodCallNode getAMethodCall() { result = this.getAUse().getAMethodCall() }

    DataFlow::CallNode getACall() { result = this.getAUse().getACall() }
  }
}
