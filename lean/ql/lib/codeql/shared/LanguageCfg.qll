private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean
private import codeql.ssa.Ssa as Ssa
private import codeql.dataflow.VariableCapture as VariableCapture

module LanguageCfgBuilder<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  private import L
  private import C
  private import MakeLanguageBase<Location, L>
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
     * If `node` is a synthetic node, this is bound to that node.
     */
    predicate isBefore(AstNode node) {
      this = node.getSyntheticChildNode("cfg-begin")
      or
      node instanceof Token and this = node
      or
      this = node.(SyntheticNode)
    }

    /**
     * Holds if this is the end of the execution of the given AST node.
     *
     * This equals the node itself since all nodes are executed in post-order,
     * but for readability it is best to use this predicate when constructing step relations.
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

  signature module LanguageCfgSig {
    predicate explicitStep(CfgNode1 node1, CfgNode2 node2);
  }

  module MakeLanguageCfg<LanguageCfgSig CfgConfig> {
    private class Node = AstNode;

    private import CfgConfig

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

    private Node getNthNode(Callable scope, int n) {
      result =
        rank[n](Node node, int line, int column, int tiebreak |
          getEnclosingCallable(node) = scope and
          ordering(node, line, column, tiebreak)
        |
          node order by line, column, tiebreak
        )
    }

    /**
     * Holds if `node1` and `node2` are adjacent in left-to-right evaluation order.
     */
    private predicate adjacent(Node node1, Node node2) {
      exists(Callable scope, int n |
        node1 = getNthNode(scope, n) and
        node2 = getNthNode(scope, n + 1)
      )
      or
      exists(Callable scope |
        node1 = getCfgEntryPoint(scope) and
        node2 = getNthNode(scope, 1)
        or
        node1 = max(int n | | getNthNode(scope, n) order by n) and
        node2 = getCfgExitPoint(scope)
      )
      or
      exists(AstNode lvalue |
        node1 = lvalue.getSyntheticChildNode("lvalue") and
        node2 = lvalue.getSyntheticChildNode("lvalue-end")
      )
    }

    /**
     * Holds if `node1 -> node2` is a step in left-to-right evaluation order that has
     * not been suppressed by an explicit step.
     */
    private predicate leftToRightStep(Node node1, Node node2) {
      adjacent(node1, node2) and
      not explicitStep(node1, _) and
      not explicitStep(_, node2)
    }

    /**
     * Holds if the CFG step from `node1` to `node2` is only taken if the value of `node1` matches `filter`.
     */
    predicate conditionalStep(Node node1, ValueFilter filter, Node node2) {
      exists(AstNode condition |
        isCondition(condition) and
        node1 = condition
      |
        node2 = getTrueOutcomeNode(condition) and
        filter = getConditionFilter(condition)
        or
        node2 = getFalseOutcomeNode(condition) and
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

    /**
     * If `node` is a conditional outcome node, gets the associated value filter.
     */
    private Node getConditionalOutcomeWithFilter(Node condition, ValueFilter filter) {
      exists(boolean outcome | result = getConditionalOutcomeNode(condition, outcome) |
        outcome = true and
        filter = getConditionFilter(condition)
        or
        outcome = false and
        filter = getConditionFilter(condition).negate()
      )
    }

    private predicate sharpenStepCandidate(Node node1, Node node2) {
      explicitStep(node1, node2)
      or
      leftToRightStep(node1, node2)
    }

    /**
     * Holds if the CFG edge `orig1 -> orig2` can safely be replaed by the more accurate `node1 -> node2`,
     * preserving more knowledge of conditional outcomes.
     */
    private predicate sharpenedStep(Node orig1, Node orig2, CfgNode1 node1, CfgNode2 node2) {
      exists(ValueFilter filter |
        logicalValueStep(orig1, orig2) and
        sharpenStepCandidate(orig1, orig2) and
        isCondition(orig2) and
        node1 = getConditionalOutcomeWithFilter(orig1, filter) and
        node2.isAfter(orig2, filter)
      )
    }

    predicate unconditionalStep(Node node1, Node node2) {
      sharpenedStep(_, _, node1, node2)
      or
      not sharpenedStep(node1, node2, _, _) and
      (
        explicitStep(node1, node2)
        or
        leftToRightStep(node1, node2) and
        not isCondition(node1)
      )
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

      class CfgScope = C::Callable;

      class Node = AstNode;

      predicate nodeGetCfgScope = getEnclosingCallable/1;

      Node nodeGetASuccessor(Node node, SuccessorType t) {
        unconditionalStep(node, result) and
        t = TSimple()
        or
        exists(AstNode condition |
          isCondition(condition) and
          node = condition
        |
          result = getTrueOutcomeNode(condition) and
          t.asBoolean() = true
          or
          result = getFalseOutcomeNode(condition) and
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

      predicate nodeIsDominanceEntry(Node node) { node = getCfgEntryPoint(_) }

      predicate nodeIsPostDominanceExit(Node node) { node = getCfgExitPoint(_) }
    }

    module BasicBlocks = BB::Make<Location, BasicBlockConfig>;

    class BasicBlock = BasicBlocks::BasicBlock;

    bindingset[node1, node2]
    pragma[inline_late]
    predicate dominates(Node node1, Node node2) {
      exists(BasicBlock bb, int i, int j |
        bb.getNode(i) = node1 and
        bb.getNode(j) = node2 and
        i < j
      )
      or
      exists(BasicBlock bb1, BasicBlock bb2 |
        bb1.getANode() = node1 and
        bb2.getANode() = node2 and
        bb1.strictlyDominates(bb2)
      )
    }

    module Debug {
      private predicate needsCfgEx(Node node) {
        needsCfg(node)
        or
        needsCfg(node.(SyntheticNode).getParent())
      }

      query predicate noSucc(AstNode node) {
        needsCfgEx(node) and
        not node = getCfgExitPoint(_) and
        not step(node, _)
      }

      query predicate noPred(AstNode node) {
        needsCfgEx(node) and
        not node = getCfgEntryPoint(_) and
        not step(_, node) and
        not step(_, getTrueOutcomeNode(node)) and
        not step(_, getFalseOutcomeNode(node))
      }

      query predicate edgeInvolvingNonCfgNode(Node node1, Node node2, string problem) {
        step(node1, node2) and
        not needsCfg(node1) and
        not node1 instanceof SyntheticNode and
        problem = "needsCfg(node1) does not hold"
        or
        step(node1, node2) and
        not needsCfg(node2) and
        not node2 instanceof SyntheticNode and
        problem = "needsCfg(node2) does not hold"
      }

      query predicate differentCfgScope(Node node1, Node node2) {
        (adjacent(node1, node2) or step(node1, node2)) and
        not getEnclosingCallable(node1) = getEnclosingCallable(node2)
      }

      query predicate noCfgScope(Node node) {
        needsCfg(node) and
        not exists(getEnclosingCallable(node))
      }

      /**
       * Holds if `node1 -> node2` is a logical value step, but there is no CFG edge from `node1 -> node2` which could be improved
       * by the logical step.
       */
      query predicate logicalStepMissingFromCfg(Node node1, Node node2) {
        logicalValueStep(node1, node2) and
        not sharpenStepCandidate(node1, node2)
      }

      query predicate logicalStepPredIsNotCondition(Node node1, Node node2, string problem) {
        logicalValueStep(node1, node2) and
        isCondition(node2) and
        not isCondition(node1) and
        problem = "node2 is a condition, but node1 is not"
      }

      query predicate counts(int numCfgNodes, int numBBs, float averageBBLength) {
        numCfgNodes = count(Node node | needsCfg(node)) and
        numBBs = count(BasicBlock b) and
        averageBBLength = numCfgNodes.(float) / numBBs.(float)
      }
    }
  }
}
