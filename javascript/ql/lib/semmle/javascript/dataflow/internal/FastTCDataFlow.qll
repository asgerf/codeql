private import javascript
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import semmle.javascript.dataflow.internal.StepSummary
private import semmle.javascript.dataflow.TypeTracking

/**
 * Gets a node that is reachable by type-tracking with a TypeTracker that has the given `prop` and `call` state.
 */
pragma[nomagic]
private DataFlow::SourceNode getANodeWithProperty(string prop, boolean call) {
  call = false and
  StepSummary::step(_, result, StoreStep(prop))
  or
  exists(StepSummary step, string prevProp, boolean prevCall |
    StepSummary::step(getANodeWithProperty(prevProp, prevCall), result, step)
  |
    step = LevelStep() and
    call = prevCall and
    prop = prevProp
    or
    step = CallStep() and
    call = true and
    prop = prevProp
    or
    step = ReturnStep() and
    prevCall = false and
    call = false and
    prop = prevProp
    or
    step = CopyStep(prevProp) and
    prop = prevProp and
    call = prevCall
    or
    step = LoadStoreStep(prevProp, prop) and
    call = prevCall
    or
    exists(PropertySet props |
      step = WithoutPropStep(props) and
      not props.getAProperty() = prevProp and
      call = prevCall and
      prop = prevProp
    )
  )
}

private newtype TIntermediateNode =
  MkIntermediateNode(DataFlow::SourceNode node, string prop) {
    node = getANodeWithProperty(prop, _)
    or
    prop = "" and exists(node)
  }

private class IntermediateNode extends TIntermediateNode {
  private string getProperty() { this = MkIntermediateNode(_, result) }

  private DataFlow::SourceNode getNode() { this = MkIntermediateNode(result, _) }

  string toString() { result = this.getNode() + " [" + this.getProperty() + "]" }

  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    this.getNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

pragma[noopt]
private predicate commonEdge(IntermediateNode pred, IntermediateNode succ) {
  exists(
    DataFlow::SourceNode predNode, DataFlow::SourceNode succNode, StepSummary step, string prop
  |
    StepSummary::step(predNode, succNode, step)
  |
    step = LoadStep(prop) and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, "")
    or
    step = StoreStep(prop) and
    pred = MkIntermediateNode(predNode, "") and
    succ = MkIntermediateNode(succNode, prop)
    or
    step = CopyStep(prop) and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, prop)
    or
    exists(string prop2 |
      step = LoadStoreStep(prop, prop2) and
      pred = MkIntermediateNode(predNode, prop) and
      succ = MkIntermediateNode(succNode, prop2)
    )
    or
    exists(PropertySet props |
      step = WithoutPropStep(props) and
      pred = MkIntermediateNode(predNode, prop) and
      succ = MkIntermediateNode(succNode, prop) and
      not prop = props.getAProperty()
    )
    or
    step = LevelStep() and
    predNode != succNode and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, prop)
  )
}

cached
private module Cached {
  pragma[noopt]
  cached
  predicate stage1Edge(IntermediateNode pred, IntermediateNode succ) {
    commonEdge(pred, succ)
    or
    exists(
      DataFlow::SourceNode predNode, DataFlow::SourceNode succNode, StepSummary step, string prop
    |
      StepSummary::step(predNode, succNode, step) and
      step = ReturnStep() and
      pred = MkIntermediateNode(predNode, prop) and
      succ = MkIntermediateNode(succNode, prop)
    )
  }

  pragma[noopt]
  cached
  predicate stage2Edge(IntermediateNode pred, IntermediateNode succ) {
    commonEdge(pred, succ)
    or
    exists(
      DataFlow::SourceNode predNode, DataFlow::SourceNode succNode, StepSummary step, string prop
    |
      StepSummary::step(predNode, succNode, step) and
      step = CallStep() and
      pred = MkIntermediateNode(predNode, prop) and
      succ = MkIntermediateNode(succNode, prop)
    )
  }
}

private import Cached

pragma[nomagic]
predicate rawNode(DataFlow::SourceNode node, IntermediateNode inode) {
  inode = MkIntermediateNode(node, "")
}

bindingset[node]
pragma[inline_late]
pragma[noopt]
DataFlow::SourceNode getAGlobalSuccessor(DataFlow::SourceNode node) {
  exists(IntermediateNode start, IntermediateNode mid, IntermediateNode end |
    rawNode(node, start) and
    stage1Edge*(start, mid) and
    stage2Edge*(mid, end) and
    rawNode(result, end)
  )
}

bindingset[node]
pragma[inline_late]
pragma[noopt]
DataFlow::SourceNode getAGlobalPredecessor(DataFlow::SourceNode node) {
  exists(IntermediateNode start, IntermediateNode mid, IntermediateNode end |
    rawNode(node, end) and
    stage2Edge*(mid, end) and
    stage1Edge*(start, mid) and
    rawNode(result, start)
  )
}

/**
 * INTERNAL. DO NOT USE.
 *
 * Used for testing.
 */
private module Internal {
  pragma[nomagic]
  private DataFlow::SourceNode getAGlobalSuccessorMaterialized(DataFlow::SourceNode node) {
    result = getAGlobalSuccessor(node)
  }

  private DataFlow::SourceNode trackNode(DataFlow::SourceNode src, DataFlow::TypeTracker t) {
    t.start() and
    result = src
    or
    exists(DataFlow::TypeTracker t2 | result = trackNode(src, t2).track(t2, t))
  }

  pragma[nomagic]
  private DataFlow::SourceNode trackNode(DataFlow::SourceNode src) {
    result = trackNode(src, DataFlow::TypeTracker::end())
  }

  pragma[noopt]
  query predicate diffWithTypeTracking(
    DataFlow::SourceNode src, DataFlow::SourceNode dst, string diff
  ) {
    dst = getAGlobalSuccessorMaterialized(src) and
    not dst = trackNode(src) and
    diff = "gained"
    or
    dst = trackNode(src) and
    not dst = getAGlobalSuccessorMaterialized(src) and
    diff = "lost"
  }
}
