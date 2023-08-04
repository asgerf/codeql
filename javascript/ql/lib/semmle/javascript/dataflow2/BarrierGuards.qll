/**
 * A copy of the barrier guard logic from `Configuration.qll` in the JS data flow library.
 *
 * This version considers all barrier guards to be relevant.
 */

private import javascript
private import semmle.javascript.dataflow.internal.AccessPaths

/**
 * Holds if data flow node `guard` acts as a barrier for data flow.
 *
 * `label` is bound to the blocked label, or the empty string if all labels should be blocked.
 */
pragma[nomagic]
private predicate barrierGuardBlocksExpr(
  DataFlow::BarrierGuardNode guard, boolean outcome, Expr test, string label
) {
  guard.blocks(outcome, test) and label = ""
  or
  guard.blocks(outcome, test, label)
  or
  // Handle labelled barrier guard functions specially, to avoid negative recursion
  // through the non-abstract 3-argument version of blocks().
  guard.(AdditionalBarrierGuardCall).internalBlocksLabel(outcome, test, label)
  or
  guard.(CallAgainstEqualityCheck).internalBlocksLabel(outcome, test, label)
}

/**
 * Holds if `guard` may block the flow of a value reachable through exploratory flow.
 */
pragma[nomagic]
private predicate barrierGuardIsRelevant(DataFlow::BarrierGuardNode guard) {
  exists(Expr e |
    barrierGuardBlocksExpr(guard, _, e, _)
    // All guards are considered relevant (this is the difference from the main JS lib)
    // isRelevantForward(e.flow(), _)
  )
}

/**
 * Holds if data flow node `guard` acts as a barrier for data flow due to aliasing through
 * an access path.
 *
 * `label` is bound to the blocked label, or the empty string if all labels should be blocked.
 */
pragma[nomagic]
private predicate barrierGuardBlocksAccessPath(
  DataFlow::BarrierGuardNode guard, boolean outcome, AccessPath ap, string label
) {
  barrierGuardIsRelevant(guard) and
  barrierGuardBlocksExpr(guard, outcome, ap.getAnInstance(), label)
}

/**
 * Holds if there exists an input variable of `ref` that blocks the label `label`.
 *
 * This predicate is outlined to give the optimizer a hint about the join ordering.
 */
pragma[nomagic]
private predicate barrierGuardBlocksSsaRefinement(
  DataFlow::BarrierGuardNode guard, boolean outcome, SsaRefinementNode ref, string label
) {
  barrierGuardIsRelevant(guard) and
  guard.getEnclosingExpr() = ref.getGuard().getTest() and
  forex(SsaVariable input | input = ref.getAnInput() |
    barrierGuardBlocksExpr(guard, outcome, input.getAUse(), label)
  )
}

/**
 * Holds if the result of `guard` is used in the branching condition `cond`.
 *
 * `outcome` is bound to the outcome of `cond` for join-ordering purposes.
 */
pragma[nomagic]
private predicate barrierGuardUsedInCondition(
  DataFlow::BarrierGuardNode guard, ConditionGuardNode cond, boolean outcome
) {
  barrierGuardIsRelevant(guard) and
  outcome = cond.getOutcome() and
  (
    cond.getTest() = guard.getEnclosingExpr()
    or
    cond.getTest().flow().getImmediatePredecessor+() = guard
  )
}

/**
 * Holds if data flow node `nd` acts as a barrier for data flow, possibly due to aliasing
 * through an access path.
 *
 * `label` is bound to the blocked label, or the empty string if all labels should be blocked.
 */
pragma[nomagic]
private predicate barrierGuardBlocksNode(
  DataFlow::BarrierGuardNode guard, DataFlow::Node nd, string label
) {
  // 1) `nd` is a use of a refinement node that blocks its input variable
  exists(SsaRefinementNode ref, boolean outcome |
    nd = DataFlow::ssaDefinitionNode(ref) and
    outcome = ref.getGuard().(ConditionGuardNode).getOutcome() and
    barrierGuardBlocksSsaRefinement(guard, outcome, ref, label)
  )
  or
  // 2) `nd` is an instance of an access path `p`, and dominated by a barrier for `p`
  exists(AccessPath p, BasicBlock bb, ConditionGuardNode cond, boolean outcome |
    nd = DataFlow::valueNode(p.getAnInstanceIn(bb)) and
    barrierGuardUsedInCondition(guard, cond, outcome) and
    barrierGuardBlocksAccessPath(guard, outcome, p, label) and
    cond.dominates(bb)
  )
}

/**
 * Gets a logical `and` expression, or parenthesized expression, that contains `guard`.
 */
private Expr getALogicalAndParent(DataFlow::BarrierGuardNode guard) {
  barrierGuardIsRelevant(guard) and result = guard.asExpr()
  or
  result.(LogAndExpr).getAnOperand() = getALogicalAndParent(guard)
  or
  result.getUnderlyingValue() = getALogicalAndParent(guard)
}

/**
 * Gets a logical `or` expression, or parenthesized expression, that contains `guard`.
 */
private Expr getALogicalOrParent(DataFlow::BarrierGuardNode guard) {
  barrierGuardIsRelevant(guard) and result = guard.asExpr()
  or
  result.(LogOrExpr).getAnOperand() = getALogicalOrParent(guard)
  or
  result.getUnderlyingValue() = getALogicalOrParent(guard)
}

/**
 * A function that returns the result of a barrier guard.
 */
private class BarrierGuardFunction extends Function {
  DataFlow::ParameterNode sanitizedParameter;
  DataFlow::BarrierGuardNode guard;
  boolean guardOutcome;
  string label;
  int paramIndex;

  BarrierGuardFunction() {
    barrierGuardIsRelevant(guard) and
    exists(Expr e |
      exists(Expr returnExpr |
        returnExpr = guard.asExpr()
        or
        // ad hoc support for conjunctions:
        getALogicalAndParent(guard) = returnExpr and guardOutcome = true
        or
        // ad hoc support for disjunctions:
        getALogicalOrParent(guard) = returnExpr and guardOutcome = false
      |
        exists(SsaExplicitDefinition ssa |
          ssa.getDef().getSource() = returnExpr and
          ssa.getVariable().getAUse() = getAReturnedExpr()
        )
        or
        returnExpr = getAReturnedExpr()
      ) and
      sanitizedParameter.flowsToExpr(e) and
      barrierGuardBlocksExpr(guard, guardOutcome, e, label)
    ) and
    sanitizedParameter.getParameter() = getParameter(paramIndex)
  }

  /**
   * Holds if this function sanitizes argument `e` of call `call`, provided the call evaluates to `outcome`.
   */
  predicate isBarrierCall(DataFlow::CallNode call, Expr e, boolean outcome, string lbl) {
    exists(DataFlow::Node arg |
      DataFlow::argumentPassingStep(pragma[only_bind_into](call), pragma[only_bind_into](arg),
        pragma[only_bind_into](this), pragma[only_bind_into](sanitizedParameter)) and
      arg.asExpr() = e and
      arg = call.getArgument(paramIndex) and
      outcome = guardOutcome and
      lbl = label
    )
  }
}

/**
 * A call that sanitizes an argument.
 */
private class AdditionalBarrierGuardCall extends DataFlow::AdditionalBarrierGuardNode,
  DataFlow::CallNode
{
  BarrierGuardFunction f;

  AdditionalBarrierGuardCall() { f.isBarrierCall(this, _, _, _) }

  override predicate blocks(boolean outcome, Expr e) { f.isBarrierCall(this, e, outcome, "") }

  predicate internalBlocksLabel(boolean outcome, Expr e, DataFlow::FlowLabel label) {
    f.isBarrierCall(this, e, outcome, label)
  }

  override predicate appliesTo(DataFlow::Configuration cfg) { none() }
}

/**
 * A sanitizer where an inner sanitizer is compared against a boolean.
 * E.g. (assuming `sanitizes(e)` is an existing sanitizer):
 * ```javascript
 * if (sanitizes(e) === true) {
 *  // e is sanitized
 * }
 * ```
 */
private class CallAgainstEqualityCheck extends DataFlow::AdditionalBarrierGuardNode {
  DataFlow::BarrierGuardNode prev;
  boolean polarity;

  CallAgainstEqualityCheck() {
    prev instanceof DataFlow::CallNode and
    exists(EqualityTest test, BooleanLiteral bool |
      this.asExpr() = test and
      test.hasOperands(prev.asExpr(), bool) and
      polarity = test.getPolarity().booleanXor(bool.getBoolValue())
    )
  }

  override predicate blocks(boolean outcome, Expr e) {
    none() // handled by internalBlocksLabel
  }

  predicate internalBlocksLabel(boolean outcome, Expr e, DataFlow::FlowLabel lbl) {
    exists(boolean prevOutcome |
      barrierGuardBlocksExpr(prev, prevOutcome, e, lbl) and
      outcome = prevOutcome.booleanXor(polarity)
    )
  }

  override predicate appliesTo(DataFlow::Configuration cfg) { none() }
}

pragma[nomagic]
predicate barrierGuardBlocksNode(DataFlow::Node nd, string label) {
  exists(DataFlow::BarrierGuardNode guard |
    barrierGuardBlocksNode(guard, nd, label) and
    // Block the AdHocWhitelistCheckSanitizer by default, as it is only used by two queries
    not guard instanceof TaintTracking::AdHocWhitelistCheckSanitizer
  )
}

pragma[nomagic]
predicate barrierGuardBlocksNodeIncludeHeuristicCheck(DataFlow::Node nd, string label) {
  exists(DataFlow::BarrierGuardNode guard | barrierGuardBlocksNode(guard, nd, label))
}
