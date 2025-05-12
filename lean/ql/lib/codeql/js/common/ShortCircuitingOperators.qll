private import All

/**
 * Gets the filter matching all values that would cause the given binary operator to short-circuit.
 *
 * For example, for `&&` this is matches all falsy values.
 *
 * For convenience this matches the operator with or without a trailing `=`.
 */
ValueFilter getShortCircuitingCondition(string operator) {
  operator = ["&&", "&&="] and result = ValueFilter::TFalsy()
  or
  operator = ["||", "||="] and result = ValueFilter::TTruthy()
  or
  operator = ["??", "??="] and result = ValueFilter::TNullLike()
}
