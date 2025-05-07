/**
 * Contains the predicates to be shared with the post-processing upgrade script.
 */

private import codeql.js.base.BaseLayer

module PostProcessing {
  predicate shouldSynthesizeNode(AstNode node, string tag) {
    LeftHandValues::isInImpureLValuePosition(node) and tag = "lvalue"
    or
    Conditions::isCondition(node) and tag = ["true-outcome", "false-outcome"]
  }
}
