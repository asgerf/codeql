private import javascript
private import semmle.javascript.dataflow2.FlowSummary

/** Holds if the given call takes a regexp containing a wildcard. */
pragma[noinline]
private predicate hasWildcardReplaceRegExp(StringReplaceCall call) {
  RegExp::isWildcardLike(call.getRegExp().getRoot().getAChild*())
}

/**
 * Summary for calls to `.replace`.
 */
private class StringReplace extends SummarizedCallable {
  StringReplace() { this = "String#replace" }

  override StringReplaceCall getACall() { any() }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = false and
    (
      input = "Argument[this]" and
      output = "ReturnValue"
      or
      input = "Argument[1].ReturnValue" and
      output = "ReturnValue"
    )
  }
}

/**
 * Summary for calls to `.replace` with a regexp pattern containing a wildcard.
 *
 * In this case, the receiver is considered to flow into the callback.
 */
private class StringReplaceWithWildcard extends SummarizedCallable {
  StringReplaceWithWildcard() { this = "String#replace with wildcard pattern" }

  override StringReplaceCall getACall() { hasWildcardReplaceRegExp(result) }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = false and
    (
      input = "Argument[this]" and
      output = "Argument[1].Parameter[0]"
      or
      input = "Argument[1].ReturnValue" and
      output = "ReturnValue"
    )
  }
}
