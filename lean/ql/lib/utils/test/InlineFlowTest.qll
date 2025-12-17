/**
 * Inline flow tests.
 * See `shared/util/codeql/dataflow/test/InlineFlowTest.qll`
 */

import codeql.js.dataflow1.All
private import codeql.Locations
private import codeql.dataflow.test.InlineFlowTest
private import internal.InlineExpectationsTestImpl

private module FlowTestImpl implements InputSig<Location, DataFlowInput> {
  import utils.test.InlineFlowTestUtil

  bindingset[src, sink]
  string getArgString(DataFlow::Node src, DataFlow::Node sink) {
    (if exists(getSourceArgString(src)) then result = getSourceArgString(src) else result = "") and
    exists(sink)
  }

  predicate interpretModelForTest(QlBuiltins::ExtensionId madId, string model) { none() }
}

import InlineFlowTestMake<Location, DataFlowInput, TaintTrackingInput, Impl, FlowTestImpl>
