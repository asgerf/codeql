/**
 * Provides modeling for the `Faraday` library.
 */

private import codeql.ruby.AST
private import codeql.ruby.CFG
private import codeql.ruby.Concepts
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowImplForHttpClientLibraries as DataFlowImplForHttpClientLibraries

private DataFlow::LocalSourceNode faradayConnection() {
  // one-off requests
  result = DataFlow::getConstant("Faraday")
  or
  // connection re-use
  result = DataFlow::getConstant("Faraday").getAMethodCall("new")
  or
  // connection re-use with Faraday::Connection.new instantiation
  result = DataFlow::getConstant("Faraday").getConstant("Connection").getAMethodCall("new")
}

/**
 * A call that makes an HTTP request using `Faraday`.
 * ```ruby
 * # one-off request
 * Faraday.get("http://example.com").body
 *
 * # connection re-use
 * connection = Faraday.new("http://example.com")
 * connection.get("/").body
 *
 * connection = Faraday.new(url: "http://example.com")
 * connection.get("/").body
 * ```
 */
class FaradayHttpRequest extends Http::Client::Request::Range, DataFlow::CallNode {
  DataFlow::LocalSourceNode connectionNode;

  FaradayHttpRequest() {
    connectionNode = faradayConnection() and
    this =
      connectionNode
          .getAMethodCall(["get", "head", "delete", "post", "put", "patch", "trace", "run_request"])
  }

  override DataFlow::Node getResponseBody() { result = this.getAMethodCall("body") }

  override DataFlow::Node getAUrlPart() {
    result = this.getArgument(0) or
    result = connectionNode.(DataFlow::CallNode).getArgument(0) or
    result = connectionNode.(DataFlow::CallNode).getKeywordArgument("url")
  }

  /** Gets the value that controls certificate validation, if any, with argument name `name`. */
  DataFlow::Node getCertificateValidationControllingValue(string argName) {
    // `Faraday::new` takes an options hash as its second argument, and we're
    // looking for
    // `{ ssl: { verify: false } }`
    // or
    // `{ ssl: { verify_mode: OpenSSL::SSL::VERIFY_NONE } }`
    argName in ["verify", "verify_mode"] and
    exists(DataFlow::Node sslValue |
      sslValue = connectionNode.(DataFlow::CallNode).getKeywordArgumentIncludeHashArgument("ssl")
    |
      exists(CfgNodes::ExprNodes::PairCfgNode p, DataFlow::Node key |
        p = sslValue.asExpr().(CfgNodes::ExprNodes::HashLiteralCfgNode).getAKeyValuePair() and
        key.asExpr() = p.getKey() and
        key.getALocalSource().asExpr().getConstantValue().isStringlikeValue(argName) and
        result.asExpr() = p.getValue()
      )
    )
  }

  cached
  override predicate disablesCertificateValidation(
    DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
  ) {
    any(FaradayDisablesCertificateValidationConfiguration config)
        .hasFlow(argumentOrigin, disablingNode) and
    disablingNode = this.getCertificateValidationControllingValue(_)
  }

  override string getFramework() { result = "Faraday" }
}

/** A configuration to track values that can disable certificate validation for Faraday. */
private class FaradayDisablesCertificateValidationConfiguration extends DataFlowImplForHttpClientLibraries::Configuration
{
  FaradayDisablesCertificateValidationConfiguration() {
    this = "FaradayDisablesCertificateValidationConfiguration"
  }

  override predicate isSource(
    DataFlow::Node source, DataFlowImplForHttpClientLibraries::FlowState state
  ) {
    source.asExpr().getExpr().(BooleanLiteral).isFalse() and
    state = "verify"
    or
    source = DataFlow::getConstant("OpenSSL").getConstant("SSL").getConstant("VERIFY_NONE") and
    state = "verify_mode"
  }

  override predicate isSink(DataFlow::Node sink, DataFlowImplForHttpClientLibraries::FlowState state) {
    sink = any(FaradayHttpRequest req).getCertificateValidationControllingValue(state)
  }
}
