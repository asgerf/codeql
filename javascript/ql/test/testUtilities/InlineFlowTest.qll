/**
 * Inline flow tests for JavaScript.
 * See `shared/util/codeql/dataflow/test/InlineFlowTest.qll`
 */

private import javascript
private import semmle.javascript.Locations
private import codeql.dataflow.test.InlineFlowTest
private import semmle.javascript.dataflow.internal.sharedlib.DataFlowArg
private import internal.InlineExpectationsTestImpl

private module FlowTestImpl implements InputSig<Location, JSDataFlow> {
  import testUtilities.InlineFlowTestUtil

  bindingset[src, sink]
  string getArgString(DataFlow::Node src, DataFlow::Node sink) {
    (if exists(getSourceArgString(src)) then result = getSourceArgString(src) else result = "") and
    exists(sink)
  }
}

import InlineFlowTestMake<Location, JSDataFlow, JSTaintFlow, Impl, FlowTestImpl>
