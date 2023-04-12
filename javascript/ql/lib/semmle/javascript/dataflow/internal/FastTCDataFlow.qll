private import javascript
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps

private module Inputs {
  predicate storeEdge(DataFlow::SourceNode pred, string prop, DataFlow::SourceNode succ) {
    exists(DataFlow::PropWrite write |
      pred = write.getRhs().getALocalSource() and
      prop = write.getPropertyName() and
      succ = write.getBase().getALocalSource()
    )
  }

  predicate loadEdge(DataFlow::SourceNode pred, string prop, DataFlow::SourceNode succ) {
    exists(DataFlow::PropRead read |
      pred = read.getBase().getALocalSource() and
      succ = read and
      prop = read.getPropertyName()
    )
  }

  predicate callEdge(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    FlowSteps::callStep(pred.getALocalUse(), succ)
  }

  predicate returnEdge(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    FlowSteps::returnStep(pred.getALocalUse(), succ)
  }
}

private DataFlow::SourceNode getANodeWithProperty(string prop, boolean call) {
  call = false and
  Inputs::storeEdge(_, prop, result)
  or
  Inputs::callEdge(getANodeWithProperty(prop, _), result) and call = true
  or
  Inputs::returnEdge(getANodeWithProperty(prop, false), result) and call = false
}

private newtype TIntermediateNode =
  MkIntermediateNode(DataFlow::SourceNode node, string prop) {
    node = getANodeWithProperty(prop, _)
    or
    prop = "" and exists(node)
  }

private class IntermediateNode extends TIntermediateNode {
  private string getProperty() { this = MkIntermediateNode(_, result) }

  private string getPropertyNonEmpty() { result = this.getProperty() and result != "" }

  private DataFlow::SourceNode getNode() { this = MkIntermediateNode(result, _) }

  string toString() { result = this.getNode() + " [" + this.getProperty() + "]" }

  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    this.getNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

pragma[noopt]
private predicate epsilonEdge(IntermediateNode pred, IntermediateNode succ) {
  exists(DataFlow::SourceNode predNode, DataFlow::SourceNode succNode, string prop |
    Inputs::loadEdge(predNode, prop, succNode) and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, "")
    or
    Inputs::storeEdge(predNode, prop, succNode) and
    pred = MkIntermediateNode(predNode, "") and
    succ = MkIntermediateNode(succNode, prop)
    or
    predNode.flowsTo(succNode) and
    predNode != succNode and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, prop)
  )
}

pragma[noopt]
private predicate stage1Edge(IntermediateNode pred, IntermediateNode succ) {
  epsilonEdge(pred, succ)
  or
  exists(DataFlow::SourceNode predNode, DataFlow::SourceNode succNode, string prop |
    Inputs::returnEdge(predNode, succNode) and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, prop)
  )
}

pragma[noopt]
private predicate stage2Edge(IntermediateNode pred, IntermediateNode succ) {
  epsilonEdge(pred, succ)
  or
  exists(DataFlow::SourceNode predNode, DataFlow::SourceNode succNode, string prop |
    Inputs::callEdge(predNode, succNode) and
    pred = MkIntermediateNode(predNode, prop) and
    succ = MkIntermediateNode(succNode, prop)
  )
}

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

predicate test(DataFlow::CallNode fetch, DataFlow::SourceNode arg) {
  arg = getAGlobalSuccessor(fetch) and
  arg != fetch
}
