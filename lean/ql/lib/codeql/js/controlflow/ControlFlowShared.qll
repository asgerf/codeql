private import javascript

signature module ControlFlowSig {
  class CfgScope;

  CfgScope getCfgScope(Node node);

  /**
   * Holds if `node` should be included in the CFG.
   *
   * Should not include synthetic nodes.
   */
  predicate needsCfg(Node node);
}

module ControlFlowShared<ExecutionOrderSig E, ControlFlowSig Config> {
  private import E
  private import Config

  class Node = AstNode;

  Node getCustomStartNode(Node node) { result = node.(ForInStatement).getRight() }

  Node getStartNode1(Node node) {
    result = getCustomStartNode(node)
    or
    isPreOrder(node) and result = node
  }

  Node getStartNode(Node node) {
    result = getStartNode1(node)
    or
    // Default to first child
    not exists(getStartNode1(node)) and
    needsCfg(node) and
    result = min(int i, Node n | js_ast_node_parent(n, node, i) | n order by i)
  }

  Node getFirstCfgNode(Node node) {
    result = getFirstCfgNode(getStartNode(node))
    or
    not exists(getStartNode(node)) and
    needsCfg(node) and
    result = node
  }

  Node getCustomLastNode(Node node) { none() }

  Node getCustomLastNode1(Node node) {
    result = getCustomLastNode(node)
    or
    not exists(getCustomLastNode(node)) and
    isPreOrder(node) and
    result = max(int i, Node n | js_ast_node_parent(n, node, i) | node order by i)
  }

  Node getLastCfgNode(Node node) {
    result = getLastCfgNode(getCustomLastNode1(node))
    or
    not exists(getCustomLastNode1(node)) and
    result = node
  }

  private int getNodeDepth(Node node) {
    not exists(node.getParent()) and result = 0
    or
    result = 1 + getNodeDepth(node.getParent())
  }

  private predicate isBeginNode(Node node) { node = E::getSyntheticBeginNode(_) }

  private predicate isEndNode(Node node) { node = E::getSyntheticEndNode(_) }

  private predicate ordering(Node node, int line, int column, int tiebreak) {
    needsCfg(node) and
    not isBeginNode(node) and
    not isEndNode(node) and
    exists(Location loc | loc = node.getLocation() |
      if isPreOrder(node)
      then (
        line = loc.getStartLine() and
        column = loc.getStartColumn() and
        tiebreak = getNodeDepth(node) * 2
      ) else (
        line = loc.getEndLine() and
        column = loc.getEndColumn() + 1 and
        tiebreak = -getNodeDepth(node) * 2
      )
    )
    or
    exists(Node island, Location loc | loc = island.getLocation() |
      node = ExecutionOrder::getSyntheticBeginNode(island) and
      line = loc.getStartLine() and
      column = loc.getStartColumn() and
      tiebreak = getNodeDepth(island) * 2 - 1 // one less than the tiebreaker for a pre-order parent
      or
      node = ExecutionOrder::getSyntheticEndNode(island) and
      line = loc.getEndLine() and
      column = loc.getEndColumn() + 1 and
      tiebreak = -getNodeDepth(island) * 2 + 1 // one higher than the tiebreaker for a post-order parent
    )
  }

  private Node getNthNode(CfgScope scope, int n) {
    result =
      rank[n](Node node, int line, int column, int tiebreak |
        getCfgScope(node) = scope and
        ordering(node, line, column, tiebreak)
      |
        node order by line, column, tiebreak
      )
  }

  private predicate adjacent(Node node1, Node node2) {
    exists(CfgScope scope, int n |
      node1 = getNthNode(scope, n) and
      node2 = getNthNode(scope, n + 1)
    )
  }

  predicate step(Node node1, Node node2) {
    adjacent(node1, node2) and
    not isBeginNode(node2) and
    not isEndNode(node1)
  }

  bindingset[node]
  Node getEnd(AstNode node) {
    result = E::getSyntheticEndNode(node)
    or
    not exists(E::getSyntheticEndNode(node)) and result = node
  }

  /**
   * Gets the would-be predecessor of `node` in the left-to-right execution order.
   *
   * This would have been the predecessor of `node` in the CFG if `node` had not been detached due to being marked
   * for out-of-order execution.
   */
  Node getDetachedPredecessor(Node node) { adjacent(result, getSyntheticBeginNode(node)) }

  /**
   * Gets the would-be successor of `node` in the left-to-right execution order.
   *
   * This would have been the successor of `node` in the CFG if `node` had not been detached due to being marked
   * for out-of-order execution.
   */
  Node getDetachedSuccessor(Node node) { adjacent(getSyntheticBeginNode(node), result) }

  module Debug {
    query predicate directBeginEndStep(
      Node node1, Node node2, Node orig1, Node orig2, int l, int c, int t, int l2, int c2, int t2,
      int l3, int c3, int t3
    ) {
      step(node1, node2) and
      isBeginNode(node1) and
      isEndNode(node2) and
      E::getSyntheticBeginNode(orig1) = node1 and
      E::getSyntheticEndNode(orig2) = node2 and
      ordering(node1, l, c, t) and
      ordering(orig1, l2, c2, t2) and
      ordering(node2, l3, c3, t3)
    }
  }
}
