/**
 * A copy of the barrier guard logic from `Configuration.qll` in the JS data flow library.
 *
 * This version considers all barrier guards to be relevant.
 */

private import javascript
private import semmle.javascript.dataflow.internal.AccessPaths

signature predicate isBarrierGuardSig(DataFlow::BarrierGuardNode node);

module MakeBarrierGuards<isBarrierGuardSig/1 isBarrierGuard> {
  final private class FinalNode = DataFlow::Node;

  abstract private class BarrierGuard extends FinalNode {
    /**
     * Holds if data flow node `guard` acts as a barrier for data flow.
     *
     * `label` is bound to the blocked label, or the empty string if all labels should be blocked.
     */
    abstract predicate blocksExpr(boolean outcome, Expr test, string label);
  }

  class ExplicitBarrierGuard extends BarrierGuard instanceof DataFlow::BarrierGuardNode {
    ExplicitBarrierGuard() {
      isBarrierGuard(this)
      or
      this instanceof DataFlow::AdditionalBarrierGuardNode
    }

    override predicate blocksExpr(boolean outcome, Expr test, string label) {
      super.blocks(outcome, test, label)
      or
      super.blocks(outcome, test) and label = ""
    }
  }

  /**
   * Holds if data flow node `guard` acts as a barrier for data flow.
   *
   * `label` is bound to the blocked label, or the empty string if all labels should be blocked.
   */
  pragma[nomagic]
  private predicate barrierGuardBlocksExpr(
    BarrierGuard guard, boolean outcome, Expr test, string label
  ) {
    guard.blocksExpr(outcome, test, label)
  }

  /**
   * Holds if `guard` may block the flow of a value reachable through exploratory flow.
   */
  pragma[nomagic]
  private predicate barrierGuardIsRelevant(BarrierGuard guard) {
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
    BarrierGuard guard, boolean outcome, AccessPath ap, string label
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
    BarrierGuard guard, boolean outcome, SsaRefinementNode ref, string label
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
    BarrierGuard guard, ConditionGuardNode cond, boolean outcome
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
  private predicate barrierGuardBlocksNode(BarrierGuard guard, DataFlow::Node nd, string label) {
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
  private Expr getALogicalAndParent(BarrierGuard guard) {
    barrierGuardIsRelevant(guard) and result = guard.asExpr()
    or
    result.(LogAndExpr).getAnOperand() = getALogicalAndParent(guard)
    or
    result.getUnderlyingValue() = getALogicalAndParent(guard)
  }

  /**
   * Gets a logical `or` expression, or parenthesized expression, that contains `guard`.
   */
  private Expr getALogicalOrParent(BarrierGuard guard) {
    barrierGuardIsRelevant(guard) and result = guard.asExpr()
    or
    result.(LogOrExpr).getAnOperand() = getALogicalOrParent(guard)
    or
    result.getUnderlyingValue() = getALogicalOrParent(guard)
  }

  final private class FinalFunction = Function;

  /**
   * A function that returns the result of a barrier guard.
   */
  private class BarrierGuardFunction extends FinalFunction {
    DataFlow::ParameterNode sanitizedParameter;
    BarrierGuard guard;
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
            ssa.getVariable().getAUse() = this.getAReturnedExpr()
          )
          or
          returnExpr = this.getAReturnedExpr()
        ) and
        sanitizedParameter.flowsToExpr(e) and
        barrierGuardBlocksExpr(guard, guardOutcome, e, label)
      ) and
      sanitizedParameter.getParameter() = this.getParameter(paramIndex)
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
  private class AdditionalBarrierGuardCall extends BarrierGuard instanceof DataFlow::CallNode {
    BarrierGuardFunction f;

    AdditionalBarrierGuardCall() { f.isBarrierCall(this, _, _, _) }

    override predicate blocksExpr(boolean outcome, Expr e, string label) {
      f.isBarrierCall(this, e, outcome, label)
    }
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
  private class CallAgainstEqualityCheck extends BarrierGuard {
    BarrierGuard prev;
    boolean polarity;

    CallAgainstEqualityCheck() {
      prev instanceof DataFlow::CallNode and
      exists(EqualityTest test, BooleanLiteral bool |
        this.asExpr() = test and
        test.hasOperands(prev.asExpr(), bool) and
        polarity = test.getPolarity().booleanXor(bool.getBoolValue())
      )
    }

    override predicate blocksExpr(boolean outcome, Expr e, string lbl) {
      exists(boolean prevOutcome |
        barrierGuardBlocksExpr(prev, prevOutcome, e, lbl) and
        outcome = prevOutcome.booleanXor(polarity)
      )
    }
  }

  pragma[nomagic]
  predicate barrierGuardBlocksNode(DataFlow::Node node, string label) {
    barrierGuardBlocksNode(_, node, label)
  }

  pragma[nomagic]
  predicate barrierGuardBlocksNode(DataFlow::Node node) { barrierGuardBlocksNode(_, node, "") }

  pragma[nomagic]
  predicate barrierGuardBlocksNodeIncludeHeuristicCheck(DataFlow::Node nd, string label) {
    exists(BarrierGuard guard | barrierGuardBlocksNode(guard, nd, label))
  }
}

module MakeSanitizerGuards<isBarrierGuardSig/1 isBarrierGuard> {
  private predicate isBarrierGuard2(DataFlow::BarrierGuardNode node) {
    isBarrierGuard(node)
    or
    node instanceof TaintTracking::AdditionalSanitizerGuardNode
  }

  import MakeBarrierGuards<isBarrierGuard2/1>
}

private predicate empty(DataFlow::BarrierGuardNode node) { none() }

module DefaultSanitizerGuards = MakeSanitizerGuards<empty/1>;

/** There are no barrier guards by default */
module DefaultBarrierGuards {
  predicate barrierGuardBlocksNode(DataFlow::Node nd, string label) { none() }

  predicate barrierGuardBlocksNode(DataFlow::Node nd) { none() }
}
