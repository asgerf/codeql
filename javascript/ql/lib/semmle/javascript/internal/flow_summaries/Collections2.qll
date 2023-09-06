/**
 * Contains flow summaries for maps, sets, and iterators.
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.FlowSummary
private import FlowSummaryUtil

private DataFlow::SourceNode mapConstructorRef() { result = DataFlow::globalVarRef("Map") }

private DataFlow::SourceNode setConstructorRef() { result = DataFlow::globalVarRef("Set") }

class IteratorNext extends SummarizedCallable {
  IteratorNext() { this = "Iterator#next" }

  override DataFlow::MethodCallNode getACallSimple() {
    result.getMethodName() = "next" and
    result.getNumArgument() = 0
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this].IteratorElement" and
    output = "ReturnValue.Member[value]"
  }
}

class MapConstructor extends SummarizedCallable {
  MapConstructor() { this = "Map constructor" }

  override DataFlow::InvokeNode getACallSimple() {
    result = mapConstructorRef().getAnInstantiation()
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[0]." + ["ArrayElement", "SetElement", "IteratorElement"] + ".Member[0]" and
      output = "ReturnValue.MapKey"
      or
      input = "Argument[0]." + ["ArrayElement", "SetElement", "IteratorElement"] + ".Member[1]" and
      output = "ReturnValue.MapValue"
      or
      input = ["Argument[0].WithMapKey", "Argument[0].WithMapValue"] and
      output = "ReturnValue"
    )
  }
}

/**
 * A read step for `Map#get`.
 *
 * This is implemented as a step instead of a flow summary, as we currently do not expose a MaD syntax
 * for map values with a known key.
 */
class MapGetStep extends DataFlow::AdditionalFlowStep {
  override predicate readStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    exists(DataFlow::MethodCallNode call |
      call.getMethodName() = "get" and
      call.getNumArgument() = 1 and
      pred = call.getReceiver() and
      succ = call
    |
      content = DataFlow2::ContentSet::mapValueFromKey(call.getArgument(0).getStringValue())
      or
      not exists(call.getArgument(0).getStringValue()) and
      content = DataFlow2::ContentSet::mapValueAll()
    )
  }
}

/**
 * A read step for `Map#set`.
 *
 * This is implemented as a step instead of a flow summary, as we currently do not expose a MaD syntax
 * for map values with a known key.
 */
class MapSetStep extends DataFlow::AdditionalFlowStep {
  override predicate storeStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    exists(DataFlow::MethodCallNode call |
      call.getMethodName() = "set" and
      call.getNumArgument() = 2 and
      pred = call.getArgument(1) and
      succ.(DataFlow::ExprPostUpdateNode).getPreUpdateNode() = call.getReceiver()
    |
      content = DataFlow2::ContentSet::mapValueFromKey(call.getArgument(0).getStringValue())
      or
      not exists(call.getArgument(0).getStringValue()) and
      content = DataFlow2::ContentSet::mapValueWithUnknownKey()
    )
  }
}

class MapGet extends SummarizedCallable {
  MapGet() { this = "Map#get" }

  override DataFlow::MethodCallNode getACallSimple() {
    none() and // Disabled for now - need MaD syntax for known map values
    result.getMethodName() = "get" and
    result.getNumArgument() = 1
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this].MapValue" and
    output = "ReturnValue"
  }
}

class MapSet extends SummarizedCallable {
  MapSet() { this = "Map#set" }

  override DataFlow::MethodCallNode getACallSimple() {
    result.getMethodName() = "set" and
    result.getNumArgument() = 2
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = ["Argument[this].WithMapKey", "Argument[this].WithMapValue"] and
    output = "ReturnValue"
    or
    preservesValue = true and
    none() and // Disabled for now - need MaD syntax for known map values
    (
      input = "Argument[0]" and
      output = "Argument[this].MapKey"
      or
      input = "Argument[1]" and
      output = "Argument[this].MapValue"
    )
  }
}

class SetConstructor extends SummarizedCallable {
  SetConstructor() { this = "Set constructor" }

  override DataFlow::InvokeNode getACallSimple() {
    result = setConstructorRef().getAnInstantiation()
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[0]." + ["ArrayElement", "SetElement", "IteratorElement"] and
      output = "ReturnValue.SetElement"
      or
      input = "Argument[0].MapKey" and
      output = "ReturnValue.SetElement.Member[0]"
      or
      input = "Argument[0].MapValue" and
      output = "ReturnValue.SetElement.Member[1]"
    )
  }
}

class SetAdd extends SummarizedCallable {
  SetAdd() { this = "Set#add" }

  override DataFlow::MethodCallNode getACallSimple() {
    result.getMethodName() = "add" and
    result.getNumArgument() = 1
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[0]" and
    output = "Argument[this].SetElement"
  }
}

class GeneratorFunctionStep extends DataFlow::AdditionalFlowStep {
  override predicate storeStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    // `yield x`. Store into the return value's iterator element.
    exists(DataFlow::FunctionNode fun, YieldExpr yield |
      fun.getFunction().isGenerator() and
      not yield.isDelegating() and
      pred = yield.getOperand().flow() and
      content = DataFlow2::ContentSet::iteratorElement() and
      succ = fun.getReturnNode()
    )
  }

  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    // `yield* x`. Flow into the return value, which has expectsContent, so only iterator elements can pass through.
    exists(DataFlow::FunctionNode fun, YieldExpr yield |
      fun.getFunction().isGenerator() and
      yield.isDelegating() and
      pred = yield.getOperand().flow() and
      succ = fun.getReturnNode()
    )
  }
}
