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
    // only track synthetic return node of async/generator functions, where it represents an allocation
    not exists(Function f |
      DataFlow::functionReturnNode(node, f) and
      not f.isAsyncOrGenerator()
    )
  }

  private predicate initialState(
    DataFlow::SourceNode node, boolean hasCall, boolean hasReturn, boolean promisified,
    int boundArgs
  ) {
    shouldTrack(node) and
    hasReturn = false and
    promisified = false and
    boundArgs = 0 and
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
  DataFlow::SourceNode trackNode(
    DataFlow::SourceNode node, boolean hasCall, boolean hasReturn, boolean promisified,
    int boundArgs
  ) {
    initialState(node, hasCall, hasReturn, promisified, boundArgs) and
    result = node
    or
    exists(DataFlow::SourceNode mid |
      mid = trackNode(node, _, hasReturn, promisified, boundArgs) and
      FlowSteps::callStep(mid.getALocalUse(), result) and
      hasCall = true
    )
    or
    exists(DataFlow::SourceNode mid |
      mid = trackNode(node, false, _, promisified, boundArgs) and
      FlowSteps::returnStep(mid.getALocalUse(), result) and
      hasReturn = true and
      hasCall = false
    )
    or
    levelStep(trackNode(node, hasCall, hasReturn, promisified, boundArgs), result)
    or
    // note: for now, mass assignment steps are simply treated as level steps
    massAssignmentStep(trackNode(node, hasCall, hasReturn, promisified, boundArgs), result)
    or
    exists(boolean call1, boolean call2, boolean return1, boolean return2 |
      derivedPropStep(trackNode(node, call1, return1, promisified, boundArgs), result, call2,
        return2) and
      call1.booleanAnd(return2) = false and
      hasCall = call1.booleanOr(call2) and
      hasReturn = return1.booleanOr(return2)
    )
    or
    // promisification
    exists(Promisify::PromisifyCall promisify |
      trackNode(node, hasCall, hasReturn, false, boundArgs).flowsTo(promisify.getArgument(0)) and
      promisified = true and
      result = promisify
    )
    or
    // partial invocation
    exists(DataFlow::PartialInvokeNode pin, DataFlow::Node pred, int predBoundArgs |
      trackNode(node, hasCall, hasReturn, promisified, predBoundArgs).flowsTo(pred) and
      result = pin.getBoundFunction(pred, boundArgs - predBoundArgs) and
      boundArgs in [0 .. 10]
    )
  }

  /**
   * Holds if `pred` can flow to `succ` via a store/load pair.
   *
   * `hasCall` and `hasReturn` indicate if the path of the carrying object contains
   * calls and returns, respectively.
   */
  pragma[nomagic]
  predicate derivedPropStep(
    DataFlow::SourceNode pred, DataFlow::SourceNode succ, boolean hasCall, boolean hasReturn
  ) {
    exists(DataFlow::SourceNode obj, string prop |
      storeStep(pred, obj, prop) and
      loadStep(trackNode(obj, hasCall, hasReturn, false, 0), succ, prop)
      or
      exists(boolean return1, boolean call1, boolean return2, boolean call2 |
        storeChain(pred, obj, call1, return1, prop) and
        loadStep(trackNode(obj, call2, return2, false, 0), succ, prop) and
        return1.booleanAnd(call2) = false and
        hasCall = call1.booleanOr(call2) and
        hasReturn = return1.booleanOr(return2)
      )
    )
  }

  /**
   * Holds if `pred` can flow to the `prop` property of `succ` via a store followed by one or
   * more load-store steps (not yet finalized by a load step).
   *
   * `hasCall` and `hasReturn` indicate if the paths of the carrying objects contain
   * calls and returns, respectively.
   */
  pragma[nomagic]
  predicate storeChain(
    DataFlow::SourceNode pred, DataFlow::SourceNode succ, boolean hasCall, boolean hasReturn,
    string prop
  ) {
    exists(DataFlow::SourceNode obj, string midProp |
      storeStep(pred, obj, midProp) and
      loadStoreStep(trackNode(obj, hasCall, hasReturn, false, 0), succ, midProp, prop)
      or
      exists(boolean call1, boolean return1, boolean call2, boolean return2 |
        storeChain(pred, obj, call1, return1, midProp) and
        loadStoreStep(trackNode(obj, call2, return2, false, 0), succ, midProp, prop) and
        return1.booleanAnd(call2) = false and
        hasCall = call1.booleanOr(call2) and
        hasReturn = return1.booleanOr(return2)
      )
    )
  }

  cached
  predicate hasFlowTo(DataFlow::SourceNode source, DataFlow::SourceNode dest) {
    trackNode(source, _, _, false, 0) = dest
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
