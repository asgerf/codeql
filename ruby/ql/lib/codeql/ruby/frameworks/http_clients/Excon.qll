/**
 * Provides modeling for the `Excon` library.
 */

private import codeql.ruby.AST
private import codeql.ruby.CFG
private import codeql.ruby.Concepts
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowImplForHttpClientLibraries as DataFlowImplForHttpClientLibraries

private DataFlow::LocalSourceNode exconConnection() {
  // one-off requests
  result = DataFlow::getConstant("Excon") or
  // connection re-use
  result = DataFlow::getConstant("Excon").getAMethodCall("new") or
  result = DataFlow::getConstant("Excon").getConstant("Connection").getAMethodCall("new")
}

/**
 * A call that makes an HTTP request using `Excon`.
 * ```ruby
 * # one-off request
 * Excon.get("http://example.com").body
 *
 * # connection re-use
 * connection = Excon.new("http://example.com")
 * connection.get(path: "/").body
 * connection.request(method: :get, path: "/")
 * ```
 *
 * TODO: pipelining, streaming responses
 * https://github.com/excon/excon/blob/master/README.md
 */
class ExconHttpRequest extends Http::Client::Request::Range, DataFlow::CallNode {
  DataFlow::LocalSourceNode connectionNode;

  ExconHttpRequest() {
    connectionNode = exconConnection() and
    this =
      connectionNode
          .getAMethodCall([
              // Excon#request exists but Excon.request doesn't.
              // This shouldn't be a problem - in real code the latter would raise NoMethodError anyway.
              "get", "head", "delete", "options", "post", "put", "patch", "trace", "request"
            ])
  }

  override DataFlow::Node getResponseBody() { result = this.getAMethodCall("body") }

  override DataFlow::Node getAUrlPart() {
    // For one-off requests, the URL is in the first argument of the request method call.
    // For connection re-use, the URL is split between the first argument of the `new` call
    // and the `path` keyword argument of the request method call.
    result = this.getArgument(0) and not result.asExpr().getExpr() instanceof Pair
    or
    result = this.getKeywordArgument("path")
    or
    result = connectionNode.(DataFlow::CallNode).getArgument(0)
  }

  /** Gets the value that controls certificate validation, if any. */
  DataFlow::Node getCertificateValidationControllingValue() {
    result =
      connectionNode.(DataFlow::CallNode).getKeywordArgumentIncludeHashArgument("ssl_verify_peer")
  }

  cached
  override predicate disablesCertificateValidation(
    DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
  ) {
    any(ExconDisablesCertificateValidationConfiguration config)
        .hasFlow(argumentOrigin, disablingNode) and
    disablingNode = this.getCertificateValidationControllingValue()
    or
    // We set `Excon.defaults[:ssl_verify_peer]` or `Excon.ssl_verify_peer` = false`
    // before the request, and no `ssl_verify_peer: true` in the explicit options hash
    // for the request call.
    exists(DataFlow::CallNode disableCall, BooleanLiteral value |
      // Excon.defaults[:ssl_verify_peer]
      disableCall = DataFlow::getConstant("Excon").getAMethodCall("defaults").getAMethodCall("[]=") and
      disableCall
          .getArgument(0)
          .getALocalSource()
          .getConstantValue()
          .isStringlikeValue("ssl_verify_peer") and
      disablingNode = disableCall.getArgument(1) and
      argumentOrigin = disablingNode.getALocalSource() and
      value = argumentOrigin.asExpr().getExpr()
      or
      // Excon.ssl_verify_peer
      disableCall = DataFlow::getConstant("Excon").getAMethodCall("ssl_verify_peer=") and
      disablingNode = disableCall.getArgument(0) and
      argumentOrigin = disablingNode.getALocalSource() and
      value = argumentOrigin.asExpr().getExpr()
    |
      value.getValue() = false and
      disableCall.asExpr().getASuccessor+() = this.asExpr() and
      // no `ssl_verify_peer: true` in the request call.
      not this.getCertificateValidationControllingValue()
          .getALocalSource()
          .asExpr()
          .getExpr()
          .(BooleanLiteral)
          .getValue() = true
    )
  }

  override string getFramework() { result = "Excon" }
}

/** A configuration to track values that can disable certificate validation for Excon. */
private class ExconDisablesCertificateValidationConfiguration extends DataFlowImplForHttpClientLibraries::Configuration
{
  ExconDisablesCertificateValidationConfiguration() {
    this = "ExconDisablesCertificateValidationConfiguration"
  }

  override predicate isSource(DataFlow::Node source) {
    source.asExpr().getExpr().(BooleanLiteral).isFalse()
  }

  override predicate isSink(DataFlow::Node sink) {
    sink = any(ExconHttpRequest req).getCertificateValidationControllingValue()
  }
}
