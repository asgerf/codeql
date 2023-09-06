/**
 * Contains flow summaries for methods with a name that can found on more than one of the core types: Array, String, Map, Set, Promise.
 *
 * This is an overview of the ambiguous methods and the classes that contain them (not all of these require a flow summary):
 * ```
 * at:           String,  Array
 * concat:       String,  Array
 * includes:     String,  Array
 * indexOf:      String,  Array
 * lastIndexOf:  String,  Array
 * slice:        String,  Array
 * entries:               Array,   Map,   Set
 * forEach:               Array,   Map,   Set
 * keys:                  Array,   Map,   Set
 * values:                Array,   Map,   Set
 * clear:                          Map,   Set
 * delete:                         Map,   Set
 * has:                            Map,   Set
 * ```
 *
 * (Promise is absent in the table above as there currently are no name clashes with Promise methods)
 */

private import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow.internal.DataFlowNode
private import semmle.javascript.dataflow2.FlowSummary
private import FlowSummaryUtil

// TODO: model iterator elements and entries(), keys(), values()
class At extends SummarizedCallable {
  At() { this = "Array#at / String#at" }

  override InstanceCall getACallSimple() { result.getMethodName() = "at" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this].ArrayElement" and
    output = "ReturnValue"
    //
    // There is no flow for String#at since we currently consider single-character extraction to be too restrictive
  }
}

class Concat extends SummarizedCallable {
  Concat() { this = "Array#concat / String#concat" }

  override InstanceCall getACallSimple() { result.getMethodName() = "concat" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this,0..].ArrayElement" and
    output = "ReturnValue.ArrayElement"
    or
    preservesValue = false and
    input = "Argument[this,0..]" and
    output = "ReturnValue"
  }
}

class Slice extends SummarizedCallable {
  Slice() { this = "Array#slice / String#slice" }

  override InstanceCall getACallSimple() { result.getMethodName() = "slice" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this].ArrayElement" and
    output = "ReturnValue.ArrayElement"
    or
    preservesValue = false and
    input = "Argument[this]" and
    output = "ReturnValue"
  }
}

class Entries extends SummarizedCallable {
  Entries() { this = "Array#entries / Map#entries / Set#entries" }

  override InstanceCall getACall() {
    result.getMethodName() = "entries" and
    result.getNumArgument() = 0
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[this]." + ["MapKey", "SetElement"] and
      output = "ReturnValue.IteratorElement.Member[0]"
      or
      input = "Argument[this]." + ["ArrayElement", "SetElement", "MapValue"] and
      output = "ReturnValue.IteratorElement.Member[1]"
    )
  }
}

class ForEach extends SummarizedCallable {
  ForEach() { this = "Array#forEach / Map#forEach / Set#forEach" }

  override InstanceCall getACallSimple() { result.getMethodName() = "forEach" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    /*
     * array.forEach(callbackfn, thisArg)
     * callbackfn(value, index, array)
     */

    (
      input = "Argument[this]." + ["ArrayElement", "SetElement", "MapValue"] and
      output = "Argument[0].Parameter[0]"
      or
      input = "Argument[this]." + ["MapKey", "SetElement"] and
      output = "Argument[0].Parameter[1]"
      or
      input = "Argument[this]" and
      output = "Argument[0].Parameter[2]" // object being iterated over
      or
      input = "Argument[1]" and // thisArg
      output = "Argument[0].Parameter[this]"
    )
  }
}

class Keys extends SummarizedCallable {
  Keys() { this = "Array#keys / Map#keys / Set#keys" }

  override InstanceCall getACallSimple() {
    result.getMethodName() = "keys" and
    result.getNumArgument() = 0
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this]." + ["MapKey", "SetElement"] and
    output = "ReturnValue.IteratorElement"
  }
}

class Values extends SummarizedCallable {
  Values() { this = "Array#values / Map#values / Set#values" }

  override InstanceCall getACallSimple() {
    result.getMethodName() = "values" and
    result.getNumArgument() = 0
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this]." + ["ArrayElement", "SetElement", "MapValue"] and
    output = "ReturnValue.IteratorElement"
  }
}

class ForOfLoopStep extends DataFlow::AdditionalFlowStep {
  override predicate readStep(
    DataFlow::Node pred, DataFlow2::ContentSet contents, DataFlow::Node succ
  ) {
    exists(ForOfStmt stmt | pred = stmt.getIterationDomain().flow() |
      contents =
        [
          DataFlow2::ContentSet::arrayElement(), DataFlow2::ContentSet::setElement(),
          DataFlow2::ContentSet::iteratorElement()
        ] and
      succ = DataFlow::lvalueNode(stmt.getLValue())
      or
      contents = DataFlow2::ContentSet::mapKey() and
      succ = TForOfSyntheticPairNode(stmt, 0)
      or
      contents = DataFlow2::ContentSet::mapValueAll() and
      succ = TForOfSyntheticPairNode(stmt, 1)
    )
  }

  override predicate storeStep(
    DataFlow::Node pred, DataFlow2::ContentSet content, DataFlow::Node succ
  ) {
    exists(ForOfStmt stmt, int i |
      pred = TForOfSyntheticPairNode(stmt, i) and
      content.asPropertyName() = i.toString() and
      succ = DataFlow::lvalueNode(stmt.getLValue())
    )
  }
}
