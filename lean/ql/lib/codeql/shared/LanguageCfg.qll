private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean

module ControlFlow<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  private import L
  private import C
  private import MakeLanguageCommon<Location, L, C>

  pragma[nomagic]
  private predicate isSubsetOf(ValueFilter a, ValueFilter b) { a.intersect(b) = a }

  private ValueFilter falsyCondition() { result = truthyCondition().negate() }

  /**
   * Gets the known outcome of a `condition` check when the chceked value is known to match `checkedValue`.
   */
  pragma[nomagic]
  private boolean getKnownOutcome(ValueFilter condition, ValueFilter checkedValue) {
    isSubsetOf(checkedValue, condition) and
    result = true
    or
    isSubsetOf(checkedValue, condition.negate()) and
    result = false
  }

  /**
   * Like `getKnownOutcome` but gets the tag of the corresponding conditional successor.
   */
  pragma[nomagic]
  private string getKnownOutcomeAsTag(ValueFilter condition, ValueFilter checkedValue) {
    result = "condition-" + getKnownOutcome(condition, checkedValue)
  }

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

    predicate isBeforeAssigningTo(AstNode lvalue) { this = lvalue.getSyntheticChildNode("lvalue") }

    predicate isAfterAssigningTo(AstNode lvalue) {
      this = lvalue.getSyntheticChildNode("lvalue-end")
    }

    string toString() { result = super.toString() }

    Location getLocation() { result = super.getLocation() }
  }

  /**
   * A node that can be used as the predecessor when constructing a CFG edge.
   */
  class CfgNode1 extends CfgNode {
    // Set bindingset to help catch missing bindings
    bindingset[this]
    CfgNode1() { any() }

    /**
     * Holds if this is the most accurate CFG node we have for the situation where execution of the given AST node
     * has just completed with a value matching `filter`.
     *
     * If `node` is not a condition, this is the same as `isAfter(node)` (i.e. we don't actually know if the value matches `filter`).
     *
     * If `node` is a condition with the given `filter`, this will be bound to the specific true/false outcome for that condition.
     *
     * If `node` is a condition with a different filter, this may bind to one of the true/false outcomes depending on the
     * subset relationship between the two filters; or it will be the same as `isAfter(node)` if nothing better can be done.
     */
    bindingset[node, filter]
    pragma[inline_late]
    predicate isAfter(AstNode node, ValueFilter filter) {
      this = node.getSyntheticChildNode(getKnownOutcomeAsTag(filter, getConditionFilter(node)))
      or
      not exists(node.getSyntheticChildNode(getKnownOutcomeAsTag(filter, getConditionFilter(node)))) and
      this.isAfter(node)
    }

    /**
     * Holds if this represents the situation where a value matching `filter` is about to be assigned to the
     * given `lvalue`.
     *
     * Currently, this must only be used when `filter` is exactly the L-value condition associated with `lvalue`
     * or its negation.
     */
    pragma[nomagic]
    predicate isBeforeAssigningTo(AstNode lvalue, ValueFilter filter) {
      // Similar logic as in the two-argument version of isAfter could be applied here, but it won't matter much in practice,
      // so just keep it simple.
      getLValueConditionFilter(lvalue) = filter and
      this = lvalue.getSyntheticChildNode("lvalue-true")
      or
      getLValueConditionFilter(lvalue) = filter.negate() and
      this = lvalue.getSyntheticChildNode("lvalue-false")
    }

    predicate isAfterTrue(AstNode node) { this.isAfter(node, truthyCondition()) }

    predicate isAfterFalse(AstNode node) { this.isAfter(node, falsyCondition()) }
  }

  /**
   * A node that can be used as the successor when constructing a CFG edge.
   */
  class CfgNode2 extends CfgNode {
    // Set bindingset to help catch missing bindings
    bindingset[this]
    CfgNode2() { any() }

    /**
     * Holds if this is the most accurate CFG node we have for the situation where execution of the given AST node
     * is going to complete with a value matching `filter`.
     *
     * If `node` is not a condition, this is the same as `isAfter(node)` (i.e. the CFG does not care if the value matches `filter`).
     *
     * If `node` is a condition with the given `filter`, this will be bound to the specific true/false outcome for that condition.
     *
     * If `node` is a condition with a different filter, this may bind to one of the true/false outcomes depending on the
     * subset relationship between the two filters; or it will be the same as `isAfter(node)` if nothing better can be done.
     */
    bindingset[node, filter]
    pragma[inline_late]
    predicate isAfter(AstNode node, ValueFilter filter) {
      // Note: the order of the arguments to 'getKnownOutcomeAsTag' is swapped here compared to CfgNode1.isAfter.
      // Here we must provide a guarantee, where in CfgNode1 we must obtain a guarantee.
      this = node.getSyntheticChildNode(getKnownOutcomeAsTag(getConditionFilter(node), filter))
      or
      not exists(node.getSyntheticChildNode(getKnownOutcomeAsTag(getConditionFilter(node), filter))) and
      this.isAfter(node)
    }

    predicate isAfterTrue(AstNode node) { this.isAfter(node, truthyCondition()) }

    predicate isAfterFalse(AstNode node) { this.isAfter(node, falsyCondition()) }
  }

  signature predicate explicitStepSig(CfgNode1 node1, CfgNode2 node2);

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

    /**
     * Holds if the CFG step from `node1` to `node2` is only taken if the value of `node1` matches `filter`.
     */
    predicate conditionalStep(Node node1, ValueFilter filter, Node node2) {
      exists(AstNode condition |
        isCondition(condition) and
        node1 = condition
      |
        node2 = condition.getSyntheticChildNode("condition-true") and
        filter = getConditionFilter(condition)
        or
        node2 = condition.getSyntheticChildNode("condition-false") and
        filter = getConditionFilter(condition).negate()
      )
      or
      exists(AstNode lvalue |
        isConditionInLValue(lvalue) and
        node1 = node1.getSyntheticChildNode("lvalue")
      |
        node2 = lvalue.getSyntheticChildNode("lvalue-true") and
        filter = getLValueConditionFilter(lvalue)
        or
        node2 = lvalue.getSyntheticChildNode("lvalue-false") and
        filter = getLValueConditionFilter(lvalue).negate()
      )
    }

    predicate unconditionalStep(Node node1, Node node2) {
      adjacent(node1, node2) and
      not explicitStep(node1, _) and
      not explicitStep(_, node2) and
      not isCondition(node1)
      or
      explicitStep(node1, node2)
    }

    predicate step(Node node1, Node node2) {
      unconditionalStep(node1, node2)
      or
      conditionalStep(node1, _, node2)
    }

    private module BasicBlockConfig implements BB::InputSig<Location> {
      private newtype TSuccessorType =
        TSimple() or
        TBoolean(Boolean b)

      class SuccessorType extends TSuccessorType {
        boolean asBoolean() { this = TBoolean(result) }

        string toString() {
          this instanceof TSimple and result = "TSimple"
          or
          result = "TBoolean(" + this.asBoolean() + ")"
        }
      }

      predicate successorTypeIsCondition(SuccessorType t) { t instanceof TBoolean }

      class CfgScope = C::CfgScope;

      class Node = AstNode;

      predicate nodeGetCfgScope = getCfgScope/1;

      Node nodeGetASuccessor(Node node, SuccessorType t) {
        unconditionalStep(node, result) and
        t = TSimple()
        or
        exists(AstNode condition |
          isCondition(condition) and
          node = condition
        |
          result = condition.getSyntheticChildNode("condition-true") and
          t.asBoolean() = true
          or
          result = condition.getSyntheticChildNode("condition-false") and
          t.asBoolean() = false
        )
        or
        exists(AstNode lvalue |
          isConditionInLValue(lvalue) and
          node = lvalue.getSyntheticChildNode("lvalue")
        |
          result = lvalue.getSyntheticChildNode("lvalue-true") and
          t.asBoolean() = true
          or
          result = lvalue.getSyntheticChildNode("lvalue-false") and
          t.asBoolean() = false
        )
      }

      predicate nodeIsDominanceEntry(Node node) { none() } // TODO

      predicate nodeIsPostDominanceExit(Node node) { none() } // TODO
    }

    module Debug {
      query predicate noSucc(AstNode node) {
        needsCfg(node) and
        not step(node, _)
      }

      query predicate noPred(AstNode node) {
        needsCfg(node) and
        not step(node, _)
      }

      //
      // Experiments with faster basic block construction due to more upfront knowledge about the CFG steps.
      //
      private predicate isJoinSlow(Node node) { strictcount(Node pred | step(pred, node)) > 1 }

      private predicate isSplitSlow(Node node) { strictcount(Node succ | step(node, succ)) > 1 }

      private predicate isJoinFast(Node node) {
        strictcount(Node pred | explicitStep(pred, node)) > 1
      }

      private predicate isSplitFast(Node node) {
        conditionalStep(node, _, _)
        or
        strictcount(Node succ | explicitStep(node, succ)) > 1
      }

      query predicate badJoinOrSplit(AstNode node, string problem) {
        isJoinSlow(node) and not isJoinFast(node) and problem = "missing join"
        or
        not isJoinSlow(node) and isJoinFast(node) and problem = "spurious join"
        or
        isSplitSlow(node) and not isSplitFast(node) and problem = "missing split"
        or
        not isSplitSlow(node) and isSplitFast(node) and problem = "spurious split"
      }
    }
  }
}
