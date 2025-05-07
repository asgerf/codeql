/**
 * Contains the predicates to be shared with the post-processing upgrade script.
 *
 * Avoid putting things here unless it is actually needed in the upgrade script.
 */

// Note: It is not possible to import arbitrary files here, since upgrades currently can't import anything.
// We special-case support for importing GeneratedAst.qll by inlining it in the generated upgrade script.
private import codeql.js.GeneratedAst
private import JS

module PostProcessing {
  predicate shouldSynthesizeNode(AstNode node, string tag) {
    LeftHandValues::isInImpureLValuePosition(node) and tag = "lvalue"
    or
    Conditions::isCondition(node) and tag = ["true-outcome", "false-outcome"]
  }
}

module LeftHandValues {
  /**
   * Holds if `node` appears in a position where it is written to and not read from.
   *
   * For example, this holds for the target of an assignment (`x = e`) but not for a compound assignment (`x += e`)
   * which is considered an impure l-value position.
   */
  predicate isInPureLValuePosition(AstNode node) {
    node = any(AssignmentExpression e).getLeft()
    or
    node = any(VariableDeclarator v).getName()
    or
    node = any(ForInStatement e).getLeft()
    or
    node = any(PairPattern p).getValue()
    or
    node = any(ArrayPattern p).getChild(_) and not node instanceof RestPattern
    or
    node = any(RestPattern p).getChild()
    // TODO: parentheses
  }

  /**
   * Holds if `node` appears in a position where it is both read from and written to.
   *
   * Concretely, this holds for the target of a compound assignment (`x += e`) or update expression (`x++`).
   */
  predicate isInImpureLValuePosition(AstNode node) {
    node = any(AugmentedAssignmentExpression e).getLeft()
    or
    node = any(UpdateExpression e).getArgument()
    // TODO: parentheses
  }

  predicate isInLValuePosition(AstNode node) {
    isInPureLValuePosition(node)
    or
    isInImpureLValuePosition(node)
  }
}

module Conditions {
  predicate isCondition(AstNode node) {
    node = any(IfStatement s).getCondition()
    or
    node = any(WhileStatement s).getCondition()
    or
    node = any(DoStatement s).getCondition()
    or
    node = any(TernaryExpression e).getCondition()
    or
    exists(UnaryExpression unary |
      unary.getOperator() = "!" and
      node = unary.getArgument()
    )
    or
    exists(BinaryExpression binary |
      binary.getOperator() = ["&&", "||", "??"] and
      node = binary.getLeft()
    )
    or
    exists(AugmentedAssignmentExpression expr |
      expr.getOperator() = ["&&=", "||=", "??="] and
      node = expr.getLeft()
    )
    or
    // The `x` in `x?.foo` needs to be checked
    node = OptionalChaining::getImmediateOptionalChainRoot(_)
  }

  pragma[nomagic]
  SyntheticNode getOutcome(AstNode node, string kind) {
    kind = ["true-outcome", "false-outcome"] and
    isCondition(node) and
    result = node.getSyntheticChildNode(kind)
  }

  pragma[nomagic]
  SyntheticNode getTrueOutcome(AstNode node) { result = getOutcome(node, "true-outcome") }

  pragma[nomagic]
  AstNode tryGetTrueOutcome(AstNode node) {
    result = getTrueOutcome(node)
    or
    not exists(getTrueOutcome(node)) and result = node
  }

  pragma[nomagic]
  SyntheticNode getFalseOutcome(AstNode node) { result = getOutcome(node, "false-outcome") }

  pragma[nomagic]
  AstNode tryGetFalseOutcome(AstNode node) {
    result = getFalseOutcome(node)
    or
    not exists(getFalseOutcome(node)) and result = node
  }
}

module OptionalChaining {
  AstNode getImmediateOptionalChainRoot(AstNode node) {
    // `object?.x`
    exists(MemberExpression member |
      node = member and
      exists(member.getOptionalChain()) and
      result = member.getObject()
    )
    or
    // `object?.[x]`
    exists(SubscriptExpression member |
      node = member and
      exists(member.getOptionalChain()) and
      result = member.getObject()
    )
    or
    // `fun?.()`
    exists(CallExpression call |
      node = call and
      exists(call.getOptionalChain()) and
      result = call.getFunction()
    )
  }

  Expression getChainBase(Expression expr) {
    result = expr.(MemberExpression).getObject()
    or
    result = expr.(SubscriptExpression).getObject()
    or
    result = expr.(CallExpression).getFunction()
  }

  AstNode getOptionalChainRoot(AstNode node) {
    result = getImmediateOptionalChainRoot(node)
    or
    not exists(getImmediateOptionalChainRoot(node)) and
    result = getOptionalChainRoot(getChainBase(node))
  }

  /**
   * The outermost accessor in an optional chain, such as `x?.y.z.w`.
   *
   * The intermediate expressions in a long chain are not instances of this class.
   */
  class OptionalChainExpression extends Expression {
    private AstNode root;

    OptionalChainExpression() {
      root = getOptionalChainRoot(this) and
      not this = getChainBase(_)
    }

    /** Gets the `x` in `x?.y.z.w` */
    AstNode getRoot() { result = root }

    /** Gets the `x?.y` in `x?.y.z.w` */
    AstNode getFirstAccessor() { getChainBase(result) = root }
  }

  predicate optionalChain(AstNode base, AstNode firstAccess, AstNode lastAccess) {
    getOptionalChainRoot(lastAccess) = base and
    not lastAccess = getChainBase(_) and
    getChainBase(firstAccess) = base
  }
}
