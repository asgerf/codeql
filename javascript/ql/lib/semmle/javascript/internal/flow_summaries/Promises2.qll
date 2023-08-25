private import javascript
private import semmle.javascript.dataflow2.FlowSummary

private DataFlow::SourceNode promiseConstructorRef() {
  result = Promises::promiseConstructorRef()
  or
  result = DataFlow::moduleImport("bluebird")
  or
  result = DataFlow::moduleMember(["q", "kew", "bluebird"], "Promise") // note: bluebird.Promise == bluebird
  or
  result = Closure::moduleImport("goog.Promise")
}

//
// Note that the 'Awaited' token has a special interpretation.
// See a write-up here: https://github.com/github/codeql-javascript-team/issues/423
//
private class PromiseConstructor extends SummarizedCallable {
  PromiseConstructor() { this = "new Promise()" }

  override DataFlow::InvokeNode getACallSimple() {
    // Disabled for now. The field-flow branch limit will be negatively affected by having
    // calls to multiple variants of `new Promise()`.
    none()
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      // TODO: not currently supported by FlowSummaryImpl.qll
      // resolve(value)
      input = "Argument[0].Parameter[0].Argument[0]" and output = "ReturnValue.Awaited"
      or
      // reject(value)
      input = "Argument[0].Parameter[1].Argument[0]" and output = "ReturnValue.Awaited[error]"
      or
      // throw from executor
      input = "Argument[0].ReturnValue[exception]" and output = "ReturnValue.Awaited[error]"
    )
  }
}

/**
 * A workaround to the `PromiseConstructor`, to be used until FlowSummaryImpl.qll has sufficient support
 * for callbacks.
 */
module PromiseConstructorWorkaround {
  class ResolveSummary extends SummarizedCallable {
    ResolveSummary() { this = "new Promise() resolve callback" }

    override DataFlow::InvokeNode getACallSimple() {
      result =
        promiseConstructorRef().getAnInstantiation().getCallback(0).getParameter(0).getACall()
    }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      preservesValue = true and
      input = "Argument[0]" and
      output = "Argument[function].Member[resolve-value]"
    }
  }

  class RejectCallback extends SummarizedCallable {
    RejectCallback() { this = "new Promise() reject callback" }

    override DataFlow::InvokeNode getACallSimple() {
      result =
        promiseConstructorRef().getAnInstantiation().getCallback(0).getParameter(1).getACall()
    }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      preservesValue = true and
      input = "Argument[0]" and
      output = "Argument[function].Member[reject-value]"
    }
  }

  class ConstructorSummary extends SummarizedCallable {
    ConstructorSummary() { this = "new Promise() workaround" }

    override DataFlow::InvokeNode getACallSimple() {
      result = promiseConstructorRef().getAnInstantiation()
    }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      preservesValue = true and
      (
        input = "Argument[0].Parameter[0].Member[resolve-value]" and
        output = "ReturnValue.Awaited"
        or
        input = "Argument[0].Parameter[1].Member[reject-value]" and
        output = "ReturnValue.Awaited[error]"
      )
    }
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
      input = "Argument[0,1].ReturnValue[exception]" and output = "ReturnValue.Awaited[error]"
      or
      input = "Argument[this].Awaited[value]" and output = "Argument[0].Parameter[0]"
      or
      input = "Argument[this].Awaited[error]" and output = "Argument[1].Parameter[0]"
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
    input = "Argument[this].WithAwaited[error]" and
    output = "ReturnValue"
  }
}

private class PromiseCatch extends SummarizedCallable {
  PromiseCatch() { this = "Promise#catch()" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = "catch" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[0].ReturnValue" and output = "ReturnValue.Awaited"
      or
      input = "Argument[0].ReturnValue[exception]" and output = "ReturnValue.Awaited[error]"
      or
      input = "Argument[this].Awaited[value]" and output = "ReturnValue.Awaited[value]"
      or
      input = "Argument[this].Awaited[error]" and output = "Argument[0].Parameter[0]"
    )
  }
}

private class PromiseFinally extends SummarizedCallable {
  PromiseFinally() { this = "Promise#finally()" }

  override DataFlow::MethodCallNode getACallSimple() { result.getMethodName() = "finally" }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      input = "Argument[0].ReturnValue.Awaited[error]" and output = "ReturnValue.Awaited[error]"
      or
      input = "Argument[0].ReturnValue[exception]" and output = "ReturnValue.Awaited[error]"
      or
      input = "Argument[this].WithAwaited[value,error]" and output = "ReturnValue"
    )
  }
}

private class PromiseResolve extends SummarizedCallable {
  PromiseResolve() { this = "Promise.resolve()" }

  override DataFlow::MethodCallNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall("resolve")
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[0]" and
    output = "ReturnValue.Awaited"
  }
}

private class PromiseReject extends SummarizedCallable {
  PromiseReject() { this = "Promise.reject()" }

  override DataFlow::MethodCallNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall("reject")
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    input = "Argument[0]" and
    output = "ReturnValue.Awaited[error]"
  }
}

private int getARelevantArrayIndex() { result = [0 .. 9] }

private string getAnArrayContent() {
  // TODO: update all uses of this predicate when we distinguish more clearly between unknown and known array indices
  result = "Member[" + getARelevantArrayIndex() + "]"
  or
  result = "ArrayElement"
}

private class PromiseAll extends SummarizedCallable {
  PromiseAll() { this = "Promise.all()" }

  override DataFlow::InvokeNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall("all")
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    exists(string content | content = getAnArrayContent() |
      input = "Argument[0]." + content + ".Awaited" and
      output = "ReturnValue.Awaited[value]." + content
      or
      input = "Argument[0]." + content + ".Awaited[error]" and
      output = "ReturnValue.Awaited[error]"
    )
  }
}

private class PromiseAnyLike extends SummarizedCallable {
  PromiseAnyLike() { this = "Promise.any() or Promise.race()" }

  override DataFlow::InvokeNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall(["any", "race", "firstFulfilled"])
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    exists(string content | content = getAnArrayContent() |
      input = "Argument[0]." + content and
      output = "ReturnValue.Awaited"
    )
  }
}

private class PromiseAllSettled extends SummarizedCallable {
  PromiseAllSettled() { this = "Promise.allSettled()" }

  override DataFlow::InvokeNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall("allSettled")
    or
    result = DataFlow::moduleImport("promise.allsettled").getACall()
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    exists(string content | content = getAnArrayContent() |
      input = "Argument[0]." + content + ".Awaited" and
      output = "ReturnValue.Awaited[value]." + content + ".Member[value]"
      or
      input = "Argument[0]." + content + ".Awaited[error]" and
      output = "ReturnValue.Awaited[value]." + content + ".Member[reason]"
    )
  }
}

private class BluebirdMapSeries extends SummarizedCallable {
  BluebirdMapSeries() { this = "bluebird.mapSeries" }

  override DataFlow::InvokeNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall("mapSeries")
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      exists(string content | content = getAnArrayContent() |
        input = "Argument[0].Awaited." + content + ".Awaited" and
        output = "Argument[1].Parameter[0]"
        or
        input = "Argument[0].Awaited." + content + ".Awaited[error]" and
        output = "ReturnValue.Awaited[error]"
      )
      or
      input = "Argument[0].WithAwaited[error]" and
      output = "ReturnValue"
      or
      input = "Argument[1].ReturnValue.Awaited" and
      output = "ReturnValue.Awaited.ArrayElement"
      or
      input = "Argument[1].ReturnValue.Awaited[error]" and
      output = "ReturnValue.Awaited[error]"
    )
  }
}

/**
 * - `Promise.withResolvers`, a method pending standardization,
 * - `goog.Closure.withResolver()` (non-plural spelling)
 * - `bluebird.Promise.defer()`
 */
private class PromiseWithResolversLike extends SummarizedCallable {
  PromiseWithResolversLike() { this = "Promise.withResolvers()" }

  override DataFlow::InvokeNode getACallSimple() {
    result = promiseConstructorRef().getAMemberCall(["withResolver", "withResolvers", "defer"])
  }

  override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    preservesValue = true and
    (
      // TODO: not currently supported by FlowSummaryImpl.qll
      input = "ReturnValue.Member[resolve].Argument[0]" and
      output = "ReturnValue.Member[promise].Awaited"
      or
      input = "ReturnValue.Member[reject].Argument[0]" and
      output = "ReturnValue.Member[promise].Awaited[error]"
    )
  }
}
