/**
 * Defines the default source and sink recognition for `InlineFlowTest.qll`.
 *
 * We reuse these predicates in some type-tracking tests that don't wish to bring in the
 * test configuration from `InlineFlowTest`.
 */

import codeql.js.dataflow1.All

predicate defaultSource(DataFlow::Node src) {
  inferNameFromNode(src.asAstNode().(CallExpression).getFunction()) = ["source", "taint"]
}

predicate defaultSink(DataFlow::Node sink) {
  exists(CallExpression mc |
    inferNameFromNode(mc.getFunction()) = "sink" and
    sink.asAstNode() = mc.getArgument(_)
  )
}

string getSourceArgString(DataFlow::Node src) {
  defaultSource(src) and
  result = getStringValueFromNode(src.asAstNode().(CallExpression).getArgument(_))
}
