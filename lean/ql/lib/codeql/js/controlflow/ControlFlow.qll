private import javascript
private import javascript as JS
private import codeql.controlflow.Cfg
private import codeql.util.Boolean
private import LeftHandValues

module ControlFlow {
  class CfgScope = FunctionOrProgram;

  int getNodeDepth(Node node) {
    not exists(node.getParent()) and result = 0
    or
    result = 1 + getNodeDepth(node.getParent())
  }

  predicate executePreOrder(Node node) { node instanceof LogicalNot }

  predicate executePostOrder(Node node) {
    not executePreOrder(node) and
    not executeAfter(node, _) and
    not executeBefore(node, _) and
    (
      node instanceof Expression
      or
      node instanceof Statement
      or
      node instanceof Program
    )
  }

  predicate executeBefore(Node node, Node other) { none() }

  predicate executeAfter(Node node, Node other) {
    exists(AssignmentExpression assign |
      node = getLValueNode(assign.getLeft()) and
      other = assign.getRight()
    )
    or
    exists(BinaryExpressionInAssignment binary |
      node = getLValueNode(binary.getAssignment().getLeft()) and
      other = binary
    )
  }

  predicate nodeOrdering(Node node, int line, int column, int tiebreak) {
    exists(Location loc | loc = node.getLocation() |
      executePostOrder(node) and
      loc = node.getLocation() and
      line = loc.getEndLine() and
      column = loc.getEndColumn() + 1 and
      tiebreak = -getNodeDepth(node) // ensure children go before their parents
      or
      executePreOrder(node) and
      line = loc.getStartLine() and
      column = loc.getStartColumn() and
      tiebreak = getNodeDepth(node) // in parent is also pre-order, make sure the parent goes first
    )
  }

  CfgScope getCfgScope(Node node) { result = getEnclosingFunctionOrProgram(node) }

  pragma[nomagic]
  private Node getNthNode(CfgScope scope, int n) {
    result =
      rank[n](Node node, int line, int column, int tiebreak |
        getCfgScope(node) = scope and
        nodeOrdering(node, line, column, tiebreak)
      |
        node order by line, column, tiebreak
      )
  }

  pragma[nomagic]
  predicate leftToRight(Node node1, Node node2) {
    exists(CfgScope scope, int n |
      node1 = getNthNode(scope, n) and
      node2 = getNthNode(scope, n + 1) and
      not suppressLeftToRightOut(node1) and
      not suppressLeftToRightIn(node2)
    )
  }

  predicate suppressLeftToRightIn(Node node) { none() }

  predicate suppressLeftToRightOut(Node node) { Conditions::isCondition(node) }
}

module ControlFlowInput implements InputSig<Location> {
  class AstNode = JS::AstNode;

  additional newtype TCompletion =
    additional TSimpleCompletion() or
    additional TBooleanCompletion(Boolean b)

  class Completion extends TCompletion {
    string toString() {
      this = TSimpleCompletion() and result = "TSimpleCompletion"
      or
      exists(boolean b | this = TBooleanCompletion(b) and result = "TBooleanCompletion(" + b + ")")
    }
  }

  predicate completionIsNormal(Completion c) { any() }

  predicate completionIsSimple(Completion c) { c = TSimpleCompletion() }

  predicate completionIsValidFor(Completion c, AstNode n) {
    if Conditions::isCondition(n) then c instanceof TBooleanCompletion else c = TSimpleCompletion()
  }

  class CfgScope = FunctionOrProgram;

  predicate getCfgScope = getEnclosingFunctionOrProgram/1;

  predicate scopeFirst(CfgScope scope, AstNode first) {
    first = scope.getSyntheticChildNode("function-entry")
  }

  predicate scopeLast(CfgScope scope, AstNode last, Completion c) {
    c = TSimpleCompletion() and
    last = scope.getSyntheticChildNode("return")
  }

  class SuccessorType = Completion;

  SuccessorType getAMatchingSuccessorType(Completion c) { result = c }

  predicate successorTypeIsSimple(SuccessorType t) { t = TSimpleCompletion() }

  predicate successorTypeIsCondition(SuccessorType t) { t instanceof TBooleanCompletion }

  predicate isAbnormalExitType(SuccessorType t) { none() }

  int idOfAstNode(AstNode node) { none() } // Not needed as this is only used for splitting internally

  int idOfCfgScope(CfgScope scope) { none() } // Not needed as this is only used for splitting internally
}
