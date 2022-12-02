/**
 * @kind path-problem
 */

import codeql.ruby.AST
import codeql.ruby.ApiGraphs
import codeql.ruby.dataflow.FlowSummary
import codeql.ruby.TaintTracking
import codeql.ruby.dataflow.internal.FlowSummaryImpl
import codeql.ruby.dataflow.internal.AccessPathSyntax
import codeql.ruby.frameworks.data.ModelsAsData
import TestUtilities.InlineFlowTest
import DataFlow::PathGraph

query predicate invalidSpecComponent(SummarizedCallable sc, string s, string c) {
  (sc.propagatesFlowExt(s, _, _) or sc.propagatesFlowExt(_, s, _)) and
  Private::External::invalidSpecComponent(s, c)
}

query predicate warning = ModelOutput::getAWarning/0;

private class SummarizedCallableIdentity extends SummarizedCallable {
  SummarizedCallableIdentity() { this = "identity" }

  override MethodCall getACall() { result.getMethodName() = this }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and
    output = "ReturnValue" and
    preservesValue = true
  }
}

private class SummarizedCallableApplyBlock extends SummarizedCallable {
  SummarizedCallableApplyBlock() { this = "apply_block" }

  override MethodCall getACall() { result.getMethodName() = this }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[0]" and
    output = "Argument[block].Parameter[0]" and
    preservesValue = true
    or
    input = "Argument[block].ReturnValue" and
    output = "ReturnValue" and
    preservesValue = true
  }
}

private class SummarizedCallableApplyLambda extends SummarizedCallable {
  SummarizedCallableApplyLambda() { this = "apply_lambda" }

  override MethodCall getACall() { result.getMethodName() = this }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    input = "Argument[1]" and
    output = "Argument[0].Parameter[0]" and
    preservesValue = true
    or
    input = "Argument[0].ReturnValue" and
    output = "ReturnValue" and
    preservesValue = true
  }
}

private class StepsFromModel extends ModelInput::SummaryModelCsv {
  override predicate row(string row) {
    row =
      [
        "any;Method[set_value];Argument[0];Argument[self].Field[@value];value",
        "any;Method[get_value];Argument[self].Field[@value];ReturnValue;value",
        "Foo.static;Method[firstArg];Argument[0];ReturnValue;taint",
        "Foo.static;Method[secondArg];Argument[1];ReturnValue;taint",
        "Foo.static;Method[onlyWithoutBlock].WithoutBlock;Argument[0];ReturnValue;taint",
        "Foo.static;Method[onlyWithBlock].WithBlock;Argument[0];ReturnValue;taint",
        "Foo.static;Method[blockArg].Argument[block].Parameter[0].Method[preserveTaint];Argument[0];ReturnValue;taint",
        "Foo.static;Method[namedArg];Argument[foo:];ReturnValue;taint",
        "Foo.static;Method[anyArg];Argument[any];ReturnValue;taint",
        "Foo.static;Method[anyNamedArg];Argument[any-named];ReturnValue;taint",
        "Foo.static;Method[anyPositionFromOne];Argument[1..];ReturnValue;taint",
        "Foo.static;Method[intoNamedCallback];Argument[0];Argument[foo:].Parameter[0];taint",
        "Foo.static;Method[intoNamedParameter];Argument[0];Argument[0].Parameter[foo:];taint",
        "Foo.static;Method[startInNamedCallback].Argument[foo:].Parameter[0].Method[preserveTaint];Argument[0];ReturnValue;taint",
        "Foo.static;Method[startInNamedParameter].Argument[0].Parameter[foo:].Method[preserveTaint];Argument[0];ReturnValue;taint",
        "Foo.instance;Method[flowToAnyArg];Argument[0];Argument[any];taint",
        "Foo.instance;Method[flowToSelf];Argument[0];Argument[self];taint",
        "any;Method[matchedByName];Argument[0];ReturnValue;taint",
        "any;Method[matchedByNameRcv];Argument[self];ReturnValue;taint",
        "any;Method[withElementOne];Argument[self].WithElement[1];ReturnValue;value",
        "any;Method[withExactlyElementOne];Argument[self].WithElement[1!];ReturnValue;value",
        "any;Method[withoutElementOne];Argument[self].WithoutElement[1];Argument[self];value",
        "any;Method[withoutExactlyElementOne];Argument[self].WithoutElement[1!];Argument[self];value",
        "any;Method[readElementOne];Argument[self].Element[1];ReturnValue;value",
        "any;Method[readExactlyElementOne];Argument[self].Element[1!];ReturnValue;value",
        "any;Method[withoutElementOneAndTwo];Argument[self].WithoutElement[1].WithoutElement[2].WithElement[any];Argument[self];value",
      ]
  }
}

private class TypeFromModel extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "~FooOrBar;Foo.instance;", //
        "~FooOrBar;Bar.instance;", //
        "~FooOrBar;~FooOrBar;Method[next].ReturnValue",
      ]
  }
}

private class TypeFromCodeQL extends ModelInput::TypeModel {
  override DataFlow::Node getASource(string type) {
    type = "~FooOrBar" and
    result.getConstantValue().getString() = "magic_string"
  }

  override API::Node getAnApiNode(string type) {
    type = "~FooOrBar" and
    result = API::getTopLevelMember("Alias").getMember(["Foo", "Bar"])
  }
}

private class InvalidTypeModel extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "TooManyColumns;;Member[Foo].Instance;too;many;columns", //
        "TooFewColumns", //
        "Foo.instance;Foo.instance;Method[foo].Arg[0]", //
        "Foo.instance;Foo.instance;Method[foo].Argument[0-1]", //
        "Foo.instance;Foo.instance;Method[foo].Argument[*]", //
        "Foo.instance;Foo.instance;Method[foo].Argument", //
        "Foo.instance;Foo.instance;Method[foo].Member", //
      ]
  }
}

private class SinkFromModel extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "~FooOrBar;Method[method].Argument[0];test-sink", //
        "Foo.static;Method[sinkAnyArg].Argument[any];test-sink", //
        "Foo.static;Method[sinkAnyNamedArg].Argument[any-named];test-sink", //
        "Foo.static;Method[getSinks].ReturnValue.Element[any].Method[mySink].Argument[0];test-sink", //
        "Foo.static;Method[arraySink].Argument[0].Element[any];test-sink", //
        "Foo.static;Method[secondArrayElementIsSink].Argument[0].Element[1];test-sink", //
      ]
  }
}

class CustomValueSink extends DefaultValueFlowConf {
  override predicate isSink(DataFlow::Node sink) {
    super.isSink(sink)
    or
    sink = ModelOutput::getASinkNode("test-sink").asSink()
  }
}

class CustomTaintSink extends DefaultTaintFlowConf {
  override predicate isSink(DataFlow::Node sink) {
    super.isSink(sink)
    or
    sink = ModelOutput::getASinkNode("test-sink").asSink()
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink, DataFlow::Configuration conf
where conf.hasFlowPath(source, sink)
select sink, source, sink, "$@", source, source.toString()
