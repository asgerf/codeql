private import All
private import codeql.shared.LanguageCommon

module LanguageCommon implements LanguageCommonSig<Location, LanguageBase> {
  import CfgScope

  class ValueFilter = ValueFilter::ValueFilter;

  ValueFilter truthyCondition() { result = ValueFilter::TTruthy() }

  ValueFilter getSpecialConditionFilter(AstNode node) {
    exists(BinaryExpressionLike binary |
      binary.getOperator() = "??" and
      result = ValueFilter::TNotNullLike()
      or
      node = binary.getRight() and
      result = getSpecialConditionFilter(binary)
    )
    or
    node = any(OptionalChainExpression e).getBase() and
    result = ValueFilter::TNotNullLike()
    or
    node instanceof AssignmentPattern and
    result = ValueFilter::TNotNullLike()
    or
    exists(ParenthesizedExpression expr |
      node = expr.getChild() and
      result = getSpecialConditionFilter(expr)
    )
  }
}

import MakeLanguageCommon<Location, LanguageBase, LanguageCommon>
