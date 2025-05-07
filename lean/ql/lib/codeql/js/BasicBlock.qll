private import javascript
private import codeql.controlflow.BasicBlock

private module Input implements InputSig<Location> {
  import ControlFlowGraph

  predicate successorTypeIsCondition(SuccessorType t) {
    t = TTrueSuccessor() or t = TFalseSuccessor()
  }

  class CfgScope = FunctionOrProgram;

  class Node = AstNode;

  predicate nodeGetCfgScope = getEnclosingFunctionOrProgram/1;

  private predicate simpleBranch(Node condition, Node trueCase, Node falseCase) {
    exists(TernaryExpression expr |
      condition = expr.getCondition() and
      trueCase = expr.getConsequence() and
      falseCase = expr.getAlternative()
    )
    or
    exists(IfStatement expr |
      condition = expr.getCondition() and
      trueCase = expr.getConsequence() and
      (
        falseCase = expr.getAlternative()
        or
        falseCase = expr.getSyntheticChildNode("false-case")
      )
    )
    or
    exists(WhileStatement stmt |
      condition = stmt.getCondition() and
      trueCase = stmt.getBody() and
      falseCase = stmt.getSyntheticChildNode("false-case")
    )
    or
    exists(DoStatement stmt |
      condition = stmt.getCondition() and
      trueCase = stmt.getBody() and
      falseCase = stmt.getSyntheticChildNode("false-case")
    )
    or
    exists(ForStatement stmt |
      condition = stmt.getCondition(0) and
      trueCase = stmt.getBody() and
      falseCase = stmt.getSyntheticChildNode("false-case")
    )
    or
    exists(ForInStatement stmt |
      condition = stmt.getSyntheticChildNode("loop-header") and
      trueCase = stmt.getBody() and
      falseCase = stmt.getSyntheticChildNode("false-case")
    )
  }

  /**
   * Like `simpleBranch`, with the additional `operator` parameter that denotes the
   * operator to be short circuited in one of the branches.
   *
   * Concretely, if a case refers to `operator` it is interpreted to mean the end of that node,
   * as opposed to its beginning.
   */
  private Node shortCircuit(Node condition, Node trueCase, Node falseCase, Node operator) {
    exists(BinaryExpressionLike binary | operator = binary |
      binary.getOperator() = "&&" and
      condition = binary.getLeft() and
      trueCase = binary.getRight() and
      falseCase = binary
      or
      binary.getOperator() = ["||", "??"] and // TODO: add nullish successor type for better precision
      condition = binary.getLeft() and
      trueCase = binary and
      falseCase = binary.getRight()
    )
  }

  private Node first(Node n) { none() }

  private predicate explicitEdge(Node node1, Node node2) {
    // The true-case and false-case synthetic nodes always go to the attached node itself
    // However, the node needs to exist so that SSA has a place to insert phi nodes in case there are other incoming edges
    exists(AstNode exprOrStmt |
      node1 = exprOrStmt.getSyntheticChildNode(["true-case", "false-case"]) and
      node2 = exprOrStmt
    )
    or
    exists(ForInStatement stmt |
      node1 = [stmt.getBody(), stmt.getRight()] and
      node2 = stmt.getSyntheticChildNode("loop-header")
    )
    or
    exists(BinaryExpressionInAssignment binary |
      if binary.getOperator() = ["&&", "||", "??"]
      then (
        // Compound lazy operators are special: the assignment only happens if the RHS
        // was evaluated; it is skipped if the condition short circuited.
        node1 = binary.getRight() and
        node2 = getLValueNode(binary.getAssignment().getLeft())
      ) else (
        node1 = binary.getLeft() and
        node2 = first(binary.getRight())
        or
        node1 = binary.getRight() and
        node2 = binary
        or
        node1 = binary and
        node2 = getLValueNode(binary.getAssignment().getLeft())
      )
    )
    or
    exists(AugmentedAssignmentExpression expr |
      node1 = expr.getLeft().getSyntheticChildNode("lvalue") and
      node2 = expr
    )
    or
    exists(UpdateExpression expr |
      node1 = expr.getArgument().getSyntheticChildNode("lvalue") and
      node2 = expr
    )
  }

  private Node branchTarget1(Node node, SuccessorType t) {
    exists(TernaryExpression expr | node = expr.getCondition() |
      t = TTrueSuccessor() and
      result = expr.getConsequence()
      or
      t = TFalseSuccessor() and
      result = expr.getAlternative()
    )
  }

  private predicate skipNode(Node node) {
    node instanceof Token and
    not node instanceof Expression and
    not node instanceof Statement
    or
    node instanceof SyntheticNode
  }

  private int getDepth(Node node) {
    not exists(node.getParent()) and result = 0
    or
    result = 1 + getDepth(node.getParent())
  }

  private int getPostOrderId(Node node, CfgScope scope) {
    node =
      rank[result](Node n, Location loc |
        n.getLocation() = loc and not skipNode(n) and nodeGetCfgScope(n) = scope
      |
        n order by loc.getEndLine(), loc.getEndColumn(), -getDepth(n)
      )
  }

  Node nodeGetASuccessor(Node node, SuccessorType t) {
    explicitEdge(node, result) and t = TNormalSuccessor()
    or
    not explicitEdge(node, _) and
    t = TNormalSuccessor() and
    leftToRightSucc(node, result)
  }

  pragma[nomagic]
  private predicate leftToRightSucc(Node node1, Node node2) {
    exists(CfgScope scope, int n |
      getPostOrderId(node1, scope) = n and
      getPostOrderId(node2, scope) = n + 1
    )
  }

  predicate nodeIsDominanceEntry(Node node) { none() }

  predicate nodeIsPostDominanceExit(Node node) { none() }

  private module Debug {
    query predicate postOrderIdClash(Node n, CfgScope f, int c, int id) {
      c = strictcount(Node n1 | getPostOrderId(n1, f) = id) and
      c > 1 and
      getPostOrderId(n, f) = id
    }
  }
}
