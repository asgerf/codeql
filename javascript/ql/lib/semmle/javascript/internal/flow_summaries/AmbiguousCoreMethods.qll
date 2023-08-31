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
      input = "Argument[this].ArrayElement" and
      output = "Argument[0].Parameter[0]"
      or
      input = "Argument[this]" and
      output = "Argument[0].Parameter[2]" // array
      or
      input = "Argument[1]" and // thisArg
      output = "Argument[0].Parameter[this]"
      //
      // TODO: Map and Set flows
    )
  }
}
