import ruby
import codeql.ruby.ast.internal.TreeSitter
import codeql.ruby.dataflow.internal.AccessPathSyntax
import codeql.ruby.frameworks.data.internal.ApiGraphModels
import codeql.ruby.ApiGraphs
import TestUtilities.InlineExpectationsTest

class AccessPathFromExpectation extends AccessPath::Range {
  AccessPathFromExpectation() { hasExpectationWithValue(_, this) }
}

API::Node evaluatePath(AccessPath path, int n) {
  path instanceof AccessPathFromExpectation and
  n = 1 and
  exists(AccessPathToken token | token = path.getToken(0) |
    token.getName() = "Member" and
    result = API::getTopLevelMember(token.getAnArgument())
    or
    token.getName() = "Method" and
    result = API::getTopLevelCall(token.getAnArgument())
    or
    token.getName() = "EntryPoint" and
    result = token.getAnArgument().(API::EntryPoint).getANode()
  )
  or
  result = getSuccessorFromNode(evaluatePath(path, n - 1), path.getToken(n - 1))
  or
  result = getSuccessorFromInvoke(evaluatePath(path, n - 1), path.getToken(n - 1))
  or
  // TODO this is a workaround, support parsing of Method['[]'] instead
  path.getToken(n - 1).getName() = "MethodBracket" and
  result = evaluatePath(path, n - 1).getMethod("[]")
}

API::Node evaluatePath(AccessPath path) { result = evaluatePath(path, path.getNumToken()) }

class ApiUseTest extends InlineExpectationsTest {
  override string getARelevantTag() { result = ["source", "sink", "call", "reachableFromSource"] }

  override predicate hasActualResult(Location location, string element, string tag, string value) {
    // All results are considered optional
    none()
  }

  override predicate hasOptionalResult(Location location, string element, string tag, string value) {
    exists(API::Node apiNode, DataFlow::Node dataflowNode |
      apiNode = evaluatePath(value) and
      (
        tag = "source" and dataflowNode = apiNode.asSource()
        or
        tag = "reachableFromSource" and dataflowNode = apiNode.getAValueReachableFromSource()
        or
        tag = "sink" and dataflowNode = apiNode.asSink()
        or
        tag = "call" and dataflowNode = apiNode.asCall()
      ) and
      location = dataflowNode.getLocation() and
      element = dataflowNode.toString()
    )
  }
}

class CustomEntryPointCall extends API::EntryPoint {
  CustomEntryPointCall() { this = "CustomEntryPointCall" }

  override DataFlow::CallNode getACall() { result.getMethodName() = "customEntryPointCall" }
}

class CustomEntryPointUse extends API::EntryPoint {
  CustomEntryPointUse() { this = "CustomEntryPointUse" }

  override DataFlow::LocalSourceNode getASource() {
    result.(DataFlow::CallNode).getMethodName() = "customEntryPointUse"
  }
}
