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
  }

  pragma[nomagic]
  private predicate storeStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ, string prop) {
    StepSummary::step(pred, succ, StoreStep(prop))
  }

  pragma[nomagic]
  private predicate loadStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ, string prop) {
    StepSummary::step(pred, succ, LoadStep(prop))
  }

  /**
   * Holds if `pred` can flow to `succ`.
   *
   * `hasCall` and `hasReturn` indicate if the path contains calls and returns, respectively.
   */
  pragma[nomagic]
  DataFlow::SourceNode trackNode(DataFlow::SourceNode node, boolean hasCall, boolean hasReturn) {
    initialState(node, hasCall, hasReturn) and
    result = node
    or
    exists(DataFlow::SourceNode mid |
      mid = trackNode(node, _, hasReturn) and
      FlowSteps::callStep(mid.getALocalUse(), result) and
      hasCall = true
    )
    or
    exists(DataFlow::SourceNode mid |
      mid = trackNode(node, false, _) and
      FlowSteps::returnStep(mid.getALocalUse(), result) and
      hasReturn = true and
      hasCall = false
    )
    or
    levelStep(trackNode(node, hasCall, hasReturn), result)
    or
    exists(boolean call1, boolean call2, boolean return1, boolean return2 |
      derivedPropStep(trackNode(node, call1, return1), result, call2, return2) and
      call1.booleanAnd(return2) = false and
      hasCall = call1.booleanOr(call2) and
      hasReturn = return1.booleanOr(return2)
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
      loadStep(trackNode(obj, hasCall, hasReturn), succ, prop)
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
    DataFlow::SourceNode getAUse() { result = trackNode(this, _, _) }

    cached
    DataFlow::SourceNode getASource() { trackNode(result, _, _) = this }

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
