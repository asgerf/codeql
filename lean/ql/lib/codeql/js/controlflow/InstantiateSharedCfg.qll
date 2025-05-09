private import javascript
private import codeql.js.controlflow.ValueFilter
private import codeql.controlflow.Cfg

class Completion = CC::Completion;

private module CC implements InputSig<Location> {
  class AstNode = Node;

  class CfgScope = FunctionOrProgram;

  predicate getCfgScope = getEnclosingFunctionOrProgram/1;

  additional newtype TCompletion =
    additional TSimpleCompletion() or
    additional TConditionalCompletion(ValueFilter filter)

  class Completion extends TCompletion {
    string toString() {
      this = TSimpleCompletion() and result = "normal"
      or
      exists(ValueFilter filter |
        this = TConditionalCompletion(filter) and result = "conditional(" + filter.toString() + ")"
      )
    }

    predicate isSimple() { this = TSimpleCompletion() }

    ValueFilter asConditional() { this = TConditionalCompletion(result) }
  }

  class SuccessorType = Completion;

  predicate completionIsNormal(Completion t) { t instanceof TSimpleCompletion }

  predicate completionIsSimple(Completion t) { t instanceof TSimpleCompletion }

  predicate completionIsValidFor(Completion c, AstNode n) {
    needsCfg(n) and
    if Conditions::isCondition(n) // TODO: restrict to the kind of check performed
    then c instanceof TConditionalCompletion
    else c = TSimpleCompletion()
  }

  /** Holds if `first` is executed first when entering `scope`. */
  predicate scopeFirst(CfgScope scope, AstNode first) {
    first = scope.(Program).getChild(0) or first = scope.(Function).getBody()
  }

  /** Holds if `scope` is exited when `last` finishes with completion `c`. */
  predicate scopeLast(CfgScope scope, AstNode last, Completion c) {
    last = max(int n | | scope.(Program).getChild(n) order by n) and c = TSimpleCompletion()
    or
    last = scope.(Function).getBody() and c = TSimpleCompletion()
  }

  /** Gets a successor type that matches completion `c`. */
  SuccessorType getAMatchingSuccessorType(Completion c) {
    c = TSimpleCompletion() and result = TSimpleCompletion()
    or
    exists(ValueFilter f1, ValueFilter f2 |
      c = TConditionalCompletion(f1) and
      result = TConditionalCompletion(f2) and
      exists(f1.intersect(f2))
    )
  }

  /**
   * Hold if `t` represents simple (normal) evaluation of a statement or an
   * expression.
   */
  predicate successorTypeIsSimple(SuccessorType t) { t = TSimpleCompletion() }

  /** Hold if `t` represents a conditional successor type. */
  predicate successorTypeIsCondition(SuccessorType t) { t instanceof TConditionalCompletion }

  /** Holds if `t` is an abnormal exit type out of a CFG scope. */
  predicate isAbnormalExitType(SuccessorType t) { none() }

  /**
   * Gets an `id` of `node`. This is used to order the predecessors of a join
   * basic block.
   */
  int idOfAstNode(AstNode node) { none() } // Ignore. Only needed for splitting features we don't use.

  /**
   * Gets an `id` of `scope`. This is used to order the predecessors of a join
   * basic block.
   */
  int idOfCfgScope(CfgScope scope) { none() } // Ignore. Only needed for splitting features we don't use.

  additional predicate needsCfg(Node node) {
    node instanceof Statement
    or
    node instanceof Expression
    or
    node instanceof Program
  }
}

module ControlFlowInstance = Make<Location, CC>;

predicate first = ControlFlowInstance::first/2;

predicate last = ControlFlowInstance::last/3;

class NodeNeedingCfg = @js_statement or @js_expression or @js_program;

abstract class CfgOverride extends ControlFlowInstance::PostOrderTree {
  pragma[nomagic]
  abstract override predicate first(AstNode first);

  override predicate propagatesAbnormal(AstNode child) { child.getParent() = this }

  pragma[nomagic]
  abstract override predicate succ(AstNode pred, AstNode succ, Completion c);
}

private class IfStatementCfg extends CfgOverride instanceof IfStatement {
  override predicate first(AstNode first) { first = super.getCondition() }

  override predicate succ(AstNode pred, AstNode succ, Completion c) {
    last(super.getCondition(), pred, c) and
    first(super.getConsequence(), succ) and
    c.asConditional() = ValueFilter::TTruthy()
    or
    last(super.getCondition(), pred, c) and
    first(super.getAlternative().getChild(), succ) and
    c.asConditional() = ValueFilter::TFalsy()
    or
    not exists(super.getAlternative()) and
    last(super.getCondition(), pred, c) and
    succ = this and
    c.asConditional() = ValueFilter::TFalsy()
    or
    last(super.getConsequence(), pred, c) and
    succ = this and
    c.isSimple()
    or
    last(super.getAlternative(), pred, c) and
    succ = this and
    c.isSimple()
  }
}
