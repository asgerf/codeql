/**
 * Contains predicates to be called from the generated post-processing upgrade script.
 */

private import codeql.js.base.BaseLayer

module PostProcessing {
  predicate shouldSynthesizeNode(AstNode node, string tag) {
    LeftHandValues::isInLValuePosition(node) and tag = ["lvalue", "lvalue-end"]
    or
    LeftHandValues::isConditionInLValue(node) and tag = ["lvalue-true", "lvalue-false"]
    or
    Conditions::isCondition(node) and tag = ["true-outcome", "false-outcome"]
    or
    node instanceof AugmentedAssignmentExpression and tag = "binary-operator"
    or
    ExecutionOrder::isExecutedOutOfOrder(node) and tag = ["begin", "end"]
    or
    ExecutionOrder::isPreOrder(node) and tag = "end"
    or
    node instanceof OptionalChaining::OptionalChainInnerAccessor and
    tag = "optionalnon-null-base-outcome"
  }
}
