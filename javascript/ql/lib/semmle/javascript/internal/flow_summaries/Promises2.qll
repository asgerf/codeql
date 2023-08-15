private import javascript
private import semmle.javascript.dataflow2.FlowSummary

//
// Note that the 'Awaited' token has a special interpretation.
// See a write-up here: https://github.com/github/codeql-javascript-team/issues/423
//
private class PromiseCreation extends SummarizedCallable {
  PromiseCreation() { this = "new Promise()" }

  override DataFlow::InvokeNode getACallSimple() { result instanceof PromiseDefinition }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      // resolve(value)
      input = "Argument[0].Parameter[0].Argument[0]" and output = "ReturnValue.Awaited"
      or
      // reject(value)
      input = "Argument[0].Parameter[1].Argument[0]" and output = "ReturnValue.AwaitedError"
      or
      // throw from executor
      input = "Argument[0].ReturnValue[exception]" and output = "ReturnValue.AwaitedError"
    )
  }
}

private class PromiseThen extends SummarizedCallable {
  PromiseThen() { this = "Promise#then()" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = "then" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[0,1].ReturnValue" and output = "ReturnValue.Awaited"
      or
      input = "Argument[0,1].ReturnValue[exception]" and output = "ReturnValue.AwaitedError"
      or
      input = "Argument[this].Awaited!" and output = "Argument[0].Parameter[0]"
      or
      input = "Argument[this].AwaitedError" and output = "Argument[1].Parameter[0]"
    )
  }
}

private class PromiseThen1Argument extends SummarizedCallable {
  PromiseThen1Argument() { this = "Promise#then() with 1 argument" }

  override DataFlow::MethodCallNode getACallSimple() {
    result.getMethodName() = "then" and
    result.getNumArgument() = 1
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[this].AwaitedError" and
    output = "ReturnValue.AwaitedError"
  }
}

private class PromiseResolve extends SummarizedCallable {
  PromiseResolve() { this = "Promise.resolve()" }

  override DataFlow::MethodCallNode getACallSimple() { result instanceof ResolvedPromiseDefinition }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[0]" and
    output = "ReturnValue.Awaited"
  }
}
