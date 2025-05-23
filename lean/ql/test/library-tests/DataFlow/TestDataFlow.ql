import codeql.js.dataflow1.All
import utils.test.InlineFlowTest
import DefaultFlowTest

query predicate foo(int x) { x = 1 }
