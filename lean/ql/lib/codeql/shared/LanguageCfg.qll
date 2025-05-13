private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean
private import codeql.ssa.Ssa as Ssa

signature module LanguageCfgSig<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  class SourceVariable {
    string toString();

    Location getLocation();
  }

  predicate isVariableRead(L::AstNode node, SourceVariable var);

  predicate isVariableWrite(L::SyntheticNode lvalueNode, SourceVariable var);

  /**
   * Holds if it is statically known that a write to `var` appears before all reads to `var`,
   * and its default initialization can therefore be omitted.
   */
  default predicate definitelyInitialized(SourceVariable var) { none() }
}

module ControlFlow<
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
      or
      exists(CfgScope scope |
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

    signature module LanguageSsaSig {
      class LocalVariable {
        VariableReference getAReference();

        string toString();

        Location getLocation();

        CfgScope getCfgScope();

        predicate isCaptured();
      }

      class VariableReference extends Node;

      default predicate assignmentIsUncertain(L::SyntheticNode lvalueNode) { none() }

      default predicate readIsUncertain(VariableReference ref) { none() }

      default predicate definitelyInitialized(LocalVariable v) { none() }
    }

    module LanguageSsa<LanguageSsaSig LanguageSsaInput> {
      private import LanguageSsaInput

      private module NonCapturedSsaConfig implements Ssa::InputSig<Location> {
        class BasicBlock = BasicBlocks::BasicBlock;

        class ControlFlowNode = AstNode;

        BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) {
          result.immediatelyDominates(bb)
        }

        BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

        final private class FinalLocalVariable = LocalVariable;

        class SourceVariable extends FinalLocalVariable {
          SourceVariable() { not this.isCaptured() }
        }

        pragma[nomagic]
        private BasicBlock getEntryBlock(CfgScope scope) {
          result.getANode() = getCfgEntryPoint(scope)
        }

        predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
          exists(Node lvalueNode |
            lvalueNode = getLValueNode(v.getAReference()) and
            bb.getNode(i) = lvalueNode and
            if assignmentIsUncertain(lvalueNode) then certain = false else certain = true
          )
          or
          // For variables that are not definitely initialized, put a synthetic initializer in the entry block
          not definitelyInitialized(v) and
          bb = getEntryBlock(v.getCfgScope()) and
          i = -1 and
          certain = true
        }

        private predicate debugLocation(Location loc) {
          exists(string file |
            loc.hasLocationInfo(file, _, _, _, _) and
            file.matches("%/apps.js")
          )
        }

        predicate variableWriteDebug(
          BasicBlock bb, int i, SourceVariable v, boolean certain, string bbStr
        ) {
          variableWrite(bb, i, v, certain) and
          v.toString() = "e" and
          debugLocation(v.getLocation()) and
          bbStr = concat(int k | | bb.getNode(k).toString(), "," order by k)
        }

        predicate bbDebug(BasicBlock bb, int i, Node node) {
          variableWriteDebug(bb, _, _, _, _) and
          node = bb.getNode(i)
        }

        predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
          exists(Node ref |
            ref = v.getAReference() and
            not isInPureLValuePosition(ref) and // not a read if pure lvalue
            bb.getNode(i) = ref and
            if readIsUncertain(ref) then certain = false else certain = true
          )
        }
      }

      import Ssa::Make<Location, NonCapturedSsaConfig>
    }

    module Debug {
      query predicate noSucc(AstNode node) {
        (needsCfg(node) or node = getTrueOutcomeNode(_) or node = getFalseOutcomeNode(_)) and
        not step(node, _) and
        not node = getCfgExitPoint(_)
      }

      query predicate noPred(AstNode node) {
        needsCfg(node) and
        not step(_, node) and
        not node = getCfgEntryPoint(_) and
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
        not getCfgScope(node1) = getCfgScope(node2)
      }

      query predicate noCfgScope(Node node) {
        needsCfg(node) and
        not exists(getCfgScope(node))
      }

      query predicate counts(int numCfgNodes, int numBBs, float averageBBLength) {
        numCfgNodes = count(Node node | needsCfg(node)) and
        numBBs = count(BasicBlock b) and
        averageBBLength = numCfgNodes.(float) / numBBs.(float)
      }
    }
  }
}
