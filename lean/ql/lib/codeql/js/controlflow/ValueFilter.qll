private import javascript

module ValueFilter {
  newtype TValueFilter =
    /**
     * Any truthy value (i.e non-falsy)
     */
    TTruthy() or
    /**
     * Any falsy value (false, null, undefined, the empty string, 0, -0, or NaN)
     */
    TFalsy() or
    /**
     * Null or undefined
     */
    TNullLike() or
    /**
     * Anything other than null or undefined
     */
    TNotNullLike()

  class ValueFilter extends TValueFilter {
    string toString() {
      this = TTruthy() and result = "truthy"
      or
      this = TFalsy() and result = "falsy"
      or
      this = TNullLike() and result = "null-like"
      or
      this = TNotNullLike() and result = "not-null-like"
    }

    private ValueFilter intersect1(ValueFilter other) {
      this = TTruthy() and other = TNotNullLike() and result = TTruthy()
      or
      this = TFalsy() and other = TNullLike() and result = TNullLike()
    }

    /**
     * Gets the filter representing the intersection of `this` and `other`.
     *
     * Has no result if no values can satisfy both filters.
     */
    ValueFilter intersect(ValueFilter other) {
      this = other and result = this
      or
      result = this.intersect1(other)
      or
      result = other.intersect1(this)
    }

    ValueFilter negate() {
      this = TTruthy() and result = TFalsy()
      or
      this = TFalsy() and result = TTruthy()
      or
      this = TNullLike() and result = TNotNullLike()
      or
      this = TNotNullLike() and result = TNullLike()
    }
  }
}

class ValueFilter = ValueFilter::ValueFilter;
