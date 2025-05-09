private import codeql.js.base.BaseLayer

/**
 * Provides mechanisms for specifying how the execution order of AST nodes deviates from the default left-to-right evaluation.
 *
 * - `isExecutedOutOfOrder` extracts a node and its subtree into its own "island" in the CFG, to be reconnected manually.
 * - `isPreOrder` causes a node to be executed before its children.
 *
 * For example, consider a tree
 * ```
 * n7
 *  - n1
 *  - n2
 *  - n5
 *    - n3
 *    - n4
 *  - n6
 * ```
 *
 * The following CFGs could be generated: (`n5` is highlighted for clarity, `*` represents synthetic begin/end nodes)
 * ```
 * Default CFG order:
 * n1 -> n2 -> n3 -> n4 -> [n5] -> n6 -> n7
 *
 * isPreOrder(n5):
 * n1 -> n2 -> [n5] -> n3 -> n4 -> n6 -> n7
 *
 * isExecutedOutOfOrder(n5):
 * n1 -> n2                        n6 -> n7
 *        * -> n3 -> n4 -> [n5] -> *
 *
 * isPreOrder(n5) and isExecutedOutOfOrder(n5):
 * n1 -> n2                        n6 -> n7
 *        * -> [n5] -> n4 -> n3 -> *
 * ```
 */
signature module ExecutionOrderSig {
  /**
   * Holds if `node` and its subtree should be extracted into its own "island" in the CFG, to be reconnected manually
   * during the CFG stage. A gap will be left between its would-be predecessor and successor.
   *
   * Synthetic `begin` and `end` nodes will be generated for `node`, which should be used as handles
   * for reconnecting it to the CFG by adding custom edges in the CFG stage.
   *
   * See `ExecutionOrderSig` for more details.
   */
  predicate isExecutedOutOfOrder(AstNode node);

  /**
   * Holds if `node` should be executed in pre-order, that is, the `node` itself
   * should appear before its children in the CFG.
   *
   * See `ExecutionOrderSig` for more details.
   */
  predicate isPreOrder(AstNode node);

  SyntheticNode getSyntheticBeginNode(AstNode node);

  SyntheticNode getSyntheticEndNode(AstNode node);
}

module ExecutionOrder implements ExecutionOrderSig {
  predicate isExecutedOutOfOrder(AstNode node) {
    node = any(IfStatement s).getConsequence()
    or
    node = any(IfStatement s).getAlternative()
    or
    node = any(WhileStatement s).getBody()
    or
    node = any(WhileStatement s).getCondition()
    or
    node = any(DoStatement s).getBody()
    or
    node = any(DoStatement s).getCondition()
    or
    node = any(ForStatement s).getInitializer()
    or
    node = any(ForStatement s).getCondition(_)
    or
    node = any(ForStatement s).getIncrement()
    or
    node = any(ForStatement s).getBody()
    or
    node = any(ForInStatement s).getBody()
    or
    node = any(ForInStatement s).getLeft()
    or
    node = any(AssignmentPattern p).getRight()
    or
    exists(BinaryExpression binary |
      binary.getOperator() = ["&&", "||", "??"] and
      node = binary.getRight()
    )
    or
    exists(AugmentedAssignmentExpression binary |
      binary.getOperator() = ["&&=", "||=", "??="] and
      node = binary.getRight()
    )
    or
    node = OptionalChaining::getImmediateOptionalChainRoot(_)
  }

  predicate isPreOrder(AstNode node) { node.(UnaryExpression).getOperator() = "!" }

  /**
   * Gets the synthetic `begin` node inserted at the beginning of a node that is to be
   * executed out of order.
   *
   * Only has results for nodes for which `isExecutedOutOfOrder` holds.
   *
   * Note that this should not be used to get the entry node of a function,
   * as it would represent a point immediately before the function's creation, not before its execution.
   */
  SyntheticNode getSyntheticBeginNode(AstNode node) {
    isExecutedOutOfOrder(node) and
    result = node.getSyntheticChildNode("begin")
  }

  /**
   * Gets the synthetic `end` node inserted at the end of a node that is to be
   * executed out of order.
   *
   * Only has results for nodes for which `isExecutedOutOfOrder` holds.
   *
   * Note that this should not be used to get the exit node of a function,
   * as it would represent a point immediately after the function's creation, not after its execution.
   */
  SyntheticNode getSyntheticEndNode(AstNode node) {
    (isExecutedOutOfOrder(node) or isPreOrder(node)) and
    result = node.getSyntheticChildNode("end")
  }
}
