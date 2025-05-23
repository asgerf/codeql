private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean
private import codeql.ssa.Ssa as Ssa
private import codeql.dataflow.VariableCapture as VariableCapture
private import codeql.util.FileSystem

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
      this = getCfgBegin(node)
      or
      not exists(getCfgBegin(node)) and
      this = node
    }

    /**
     * Holds if this is the end of the execution of the given AST node.
     *
     * This equals the node itself since all nodes are executed in post-order,
     * but for readability it is best to use this predicate when constructing step relations.
     */
    predicate isAfter(AstNode node) { this = node }

    predicate isBeforeAssigningTo(AstNode lvalue) { this = getLValueNode(lvalue) }

    predicate isAfterAssigningTo(AstNode lvalue) { this = getLValueEndNode(lvalue) }

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
    /**
     * Holds if the given `node` and its subtree should be evaluated in the initializer block of its enclosing callable.
     *
     * Within the initializer block, nodes are evaluated left-to-right according to their location.
     *
     * Typically this is used to place synthetic parameters at the initializer block.
     */
    predicate hoistToInitializerBlock(AstNode node);

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

    bindingset[node1, node2]
    pragma[inline_late]
    private predicate sameCallable(Node node1, Node node2) {
      getEnclosingCallable(node1) = getEnclosingCallable(node2)
    }

    private predicate isHoisted(Node node) {
      hoistToInitializerBlock(node)
      or
      not node instanceof SyntheticNode and
      exists(Node parent |
        parent = node.getParent() and
        isHoisted(parent) and
        sameCallable(node, parent)
      )
    }

    int getHoistingRank(Node node) { if isHoisted(node) then result = -1 else result = 1 }

    private predicate ordering(Node node, int line, int column, int tiebreak) {
      (needsCfg(node) or isHoisted(node)) and
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
          node order by getHoistingRank(node), line, column, tiebreak
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

    /** A node to be included in the output of `TestOutput`. */
    signature class RelevantNodeSig extends Node;

    /**
     * Import this module into a `.ql` file to output a CFG. The
     * graph is restricted to nodes from `RelevantNode`.
     */
    module TestOutput<RelevantNodeSig RelevantNode> {
      /** Holds if `pred -> succ` is an edge in the CFG. */
      query predicate edges(RelevantNode pred, RelevantNode succ, string label) {
        exists(ValueFilter filter |
          conditionalStep(pred, filter, succ) and
          label = filter.toString()
        )
        or
        unconditionalStep(pred, succ) and label = ""
      }

      /**
       * Provides logic for representing a CFG as a [Mermaid diagram](https://mermaid.js.org/).
       */
      module Mermaid {
        private string nodeId(RelevantNode n) {
          result =
            any(int i |
              n =
                rank[i](RelevantNode p, string filePath, int startLine, int startColumn,
                  int endLine, int endColumn |
                  p.getLocation()
                      .hasLocationInfo(filePath, startLine, startColumn, endLine, endColumn)
                |
                  p order by filePath, startLine, startColumn, endLine, endColumn, p.toString()
                )
            ).toString()
        }

        private string nodes() {
          result =
            concat(RelevantNode n, string id, string text |
              id = nodeId(n) and
              text = n.toString()
            |
              id + "[\"" + text + "\"]", "\n" order by id
            )
        }

        private string edge(RelevantNode pred, RelevantNode succ) {
          edges(pred, succ, _) and
          exists(string label |
            edges(pred, succ, label) and
            if label = ""
            then result = nodeId(pred) + " --> " + nodeId(succ)
            else result = nodeId(pred) + " -- " + label + " --> " + nodeId(succ)
          )
        }

        private string edges() {
          result =
            concat(RelevantNode pred, RelevantNode succ, string edge, string filePath,
              int startLine, int startColumn, int endLine, int endColumn |
              edge = edge(pred, succ) and
              pred.getLocation()
                  .hasLocationInfo(filePath, startLine, startColumn, endLine, endColumn)
            |
              edge, "\n"
              order by
                filePath, startLine, startColumn, endLine, endColumn, pred.toString()
            )
        }

        /** Holds if the Mermaid representation is `s`. */
        query predicate mermaid(string s) { s = "flowchart TD\n" + nodes() + "\n\n" + edges() }
      }
    }

    /** Provides the input to `ViewCfgQuery`. */
    signature module ViewCfgQueryInputSig<FileSig File> {
      /** The source file selected in the IDE. Should be an `external` predicate. */
      string selectedSourceFile();

      /** The source line selected in the IDE. Should be an `external` predicate. */
      int selectedSourceLine();

      /** The source column selected in the IDE. Should be an `external` predicate. */
      int selectedSourceColumn();

      File getFileFromLocation(Location loc);
    }

    /**
     * Provides an implementation for a `View CFG` query.
     *
     * Import this module into a `.ql` that looks like
     *
     * ```ql
     * @name Print CFG
     * @description Produces a representation of a file's Control Flow Graph.
     *              This query is used by the VS Code extension.
     * @id <lang>/print-cfg
     * @kind graph
     * @tags ide-contextual-queries/print-cfg
     * ```
     */
    module ViewCfgQuery<FileSig File, ViewCfgQueryInputSig<File> ViewCfgQueryInput> {
      private import ViewCfgQueryInput

      predicate callableSpan(
        Callable callable, File file, int startLine, int startColumn, int endLine, int endColumn
      ) {
        exists(Location loc |
          loc = callable.getLocation() and
          file = getFileFromLocation(callable.getLocation()) and
          loc.hasLocationInfo(_, startLine, startColumn, endLine, endColumn)
        )
      }

      bindingset[file, line, column]
      private Callable smallestEnclosingScope(File file, int line, int column) {
        result =
          min(Callable scope, int startLine, int startColumn, int endLine, int endColumn |
            callableSpan(scope, file, startLine, startColumn, endLine, endColumn) and
            (
              startLine < line
              or
              startLine = line and startColumn <= column
            ) and
            (
              endLine > line
              or
              endLine = line and endColumn >= column
            )
          |
            scope order by startLine desc, startColumn desc, endLine, endColumn
          )
      }

      private import IdeContextual<File>

      final private class FinalAstNode = AstNode;

      private class RelevantNode extends FinalAstNode {
        RelevantNode() {
          getEnclosingCallable(this) =
            smallestEnclosingScope(getFileBySourceArchiveName(selectedSourceFile()),
              selectedSourceLine(), selectedSourceColumn())
        }

        string getOrderDisambiguation() { result = "" }
      }

      private module Output = TestOutput<RelevantNode>;

      import Output::Mermaid

      /** Holds if `pred` -> `succ` is an edge in the CFG. */
      query predicate edges(RelevantNode pred, RelevantNode succ, string attr, string val) {
        attr = "semmle.label" and
        Output::edges(pred, succ, val)
      }
    }
  }
}
