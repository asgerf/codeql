private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.js.controlflow.ValueFilter

module ControlFlow<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  private import L
  private import C

  class CfgNode instanceof AstNode {
    // Set bindingset to help catch missing bindings
    bindingset[this]
    CfgNode() { any() }

    /**
     * Holds if this is the beginning of the execution of the given AST node.
     *
     * Has no result for synthetic nodes. Use those directly instead.
     */
    predicate isBefore(AstNode node) {
      this = node.getSyntheticChildNode("cfg-begin")
      or
      node instanceof Token and this = node
    }

    /**
     * Holds if this is the end of the execution of the given AST node.
     *
     * This equals the node itself since all nodes are executed in post-order,
     * but for readability this is best to use this predicate when constructing step relations.
     */
    predicate isAfter(AstNode node) { this = node }

    predicate isAfterTrue(AstNode node) {
      isCondition(node) and
      this = node.getSyntheticChildNode("true-outcome")
    }

    predicate isAfterFalse(AstNode node) {
      isCondition(node) and
      this = node.getSyntheticChildNode("false-outcome")
    }

    predicate isAfterValueIs(AstNode node, ValueFilter filter) {
      isCondition(node) and
      this = node.getSyntheticChildNode("true-outcome")
    }

    predicate isAfterShortCircuit(AstNode node) { this.isAfterTrue(node) }

    predicate isAfterNoShortCircuit(AstNode node) { this.isAfterFalse(node) }

    predicate isBeforeAssigningTo(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue") }

    predicate isBeforeAssigningToTrue(AstNode lvalue) {
      this = lvalue.getSyntheticChildNode("lvalue-true")
    }

    predicate isBeforeAssigningToFalse(AstNode lvalue) {
      this = lvalue.getSyntheticChildNode("lvalue-false")
    }

    predicate isAfterAssigningTo(AstNode lvalue) {
      this = lvalue.getSyntheticChildNode("lvalue-end")
    }

    string toString() { result = super.toString() }

    Location getLocation() { result = super.getLocation() }
  }

  signature predicate explicitStepSig(CfgNode node1, CfgNode node2);

  module MakeCfg<explicitStepSig/2 explicitStep> {
    private class Node = AstNode;

    private int getNodeDepth(Node node) {
      not exists(node.getParent()) and result = 0
      or
      result = 1 + getNodeDepth(node.getParent())
    }

    private predicate isSyntheticBeginNode(SyntheticNode node) { node.getTag() = "cfg-begin" }

    private predicate ordering(Node node, int line, int column, int tiebreak) {
      needsCfg(node) and
      not isSyntheticBeginNode(node) and
      exists(Location loc | loc = node.getLocation() |
        line = loc.getEndLine() and
        column = loc.getEndColumn() + 1 and
        tiebreak = -getNodeDepth(node)
      )
      or
      exists(Node orig, Location loc |
        node = orig.getSyntheticChildNode("cfg-begin") and
        loc = orig.getLocation() and
        line = loc.getStartLine() and
        column = loc.getStartColumn() and
        tiebreak = getNodeDepth(orig)
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

    /**
     * Holds if `node1` and `node2` are adjacent in left-to-right evaluation order.
     */
    private predicate adjacent(Node node1, Node node2) {
      exists(CfgScope scope, int n |
        node1 = getNthNode(scope, n) and
        node2 = getNthNode(scope, n + 1)
      )
    }

    private predicate stepEx(Node node1, Node node2) {
      isCondition(node1) and
      node1.getSyntheticChildNode(["true-outcome", "false-outcome"]) = node2 and
      not explicitStep(_, node2)
    }

    predicate step(Node node1, Node node2) {
      adjacent(node1, node2) and
      not explicitStep(node1, _) and
      not explicitStep(_, node2)
      or
      explicitStep(node1, node2)
    }
  }
}
