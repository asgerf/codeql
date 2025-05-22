private import All
private import codeql.shared.LanguageCommon

module LanguageCommon implements LanguageCommonSig<Location, LanguageBase> {
  import CfgScope
  import Callable

  class ValueFilter = ValueFilter::ValueFilter;

  ValueFilter truthyCondition() { result = ValueFilter::TTruthy() }

  ValueFilter getSpecialConditionFilter(AstNode node) {
    exists(BinaryExpressionLike binary |
      node = binary.getLeft() and
      binary.getOperator() = "??" and
      result = ValueFilter::TNotNullLike()
    )
    or
    node = any(OptionalChainExpression e).getBase() and
    result = ValueFilter::TNotNullLike()
    or
    node instanceof AssignmentPattern and
    result = ValueFilter::TNotNullLike()
  }

  predicate logicalValueStep(AstNode node1, AstNode node2) {
    exists(BinaryExpressionLike expr | expr.getOperator() = ["||", "??", "&&"] |
      node1 = expr.getRight() and
      node2 = expr
    )
    or
    exists(TernaryExpression expr |
      node1 = [expr.getConsequence(), expr.getAlternative()] and
      node2 = expr
    )
    or
    exists(ParenthesizedExpression expr |
      node1 = expr.getChild() and
      node2 = expr
    )
    or
    exists(SequenceExpression expr |
      node1 = max(int i | | expr.getChild(i) order by i) and
      node2 = expr
    )
  }
}

import MakeLanguageCommon<Location, LanguageBase, LanguageCommon>
