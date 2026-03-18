/**
 * Defines the default source and sink recognition for `InlineFlowTest.qll`.
 *
 * We reuse these predicates in some type-tracking tests that don't wish to bring in the
 * test configuration from `InlineFlowTest`.
 */

private import semmle.javascript.internal.unified.minimal.minimal
private import semmle.javascript.internal.unified.JSUnified

predicate defaultSource(DataFlow::Node src) {
  exists(InvokeExpr call |
    call.getCalleeName() = "source" and
    src.isValueOf(call)
  )
}

predicate defaultSink(DataFlow::Node sink) {
  exists(InvokeExpr call |
    call.getCalleeName() = "sink" and
    sink.isValueOf(call.getAnArgument())
  )
}

bindingset[src]
string getSourceArgString(DataFlow::Node src) {
  result = src.asAstNode().(InvokeExpr).getAnArgument().getStringValue()
}
