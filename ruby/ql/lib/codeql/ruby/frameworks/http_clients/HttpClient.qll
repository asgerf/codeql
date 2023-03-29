/**
 * Provides modeling for the `HTTPClient` library.
 */

private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowImplForHttpClientLibraries as DataFlowImplForHttpClientLibraries

private DataFlow::LocalSourceNode httpConnection() {
  // One-off requests
  result = DataFlow::getConstant("HTTPClient")
  or
  // Connection re-use
  result = DataFlow::getConstant("HTTPClient").getAMethodCall("new")
}

/**
 * A call that makes an HTTP request using `HTTPClient`.
 * ```ruby
 * HTTPClient.get("http://example.com").body
 * HTTPClient.get_content("http://example.com")
 * ```
 */
class HttpClientRequest extends Http::Client::Request::Range, DataFlow::CallNode {
  DataFlow::LocalSourceNode connectionNode;

  HttpClientRequest() {
    connectionNode = httpConnection() and
    this =
      connectionNode
          .getAMethodCall([
              "get", "head", "delete", "options", "post", "put", "trace", "get_content",
              "post_content"
            ])
  }

  override DataFlow::Node getAUrlPart() { result = this.getArgument(0) }

  override DataFlow::Node getResponseBody() {
    // The `get_content` and `post_content` methods return the response body as
    // a string. The other methods return a `HTTPClient::Message` object which
    // has various methods that return the response body.
    this.getMethodName() in ["get_content", "post_content"] and result = this
    or
    not this.getMethodName() in ["get_content", "put_content"] and
    result = this.getAMethodCall(["body", "http_body", "content", "dump"])
  }

  /** Gets the value that controls certificate validation, if any. */
  DataFlow::Node getCertificateValidationControllingValue() {
    // Look for calls to set
    // `c.ssl_config.verify_mode = OpenSSL::SSL::VERIFY_NONE`
    // on an HTTPClient connection object `c`.
    result =
      connectionNode.getAMethodCall("ssl_config").getAMethodCall("verify_mode=").getArgument(0)
  }

  cached
  override predicate disablesCertificateValidation(
    DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
  ) {
    any(HttpClientDisablesCertificateValidationConfiguration config)
        .hasFlow(argumentOrigin, disablingNode) and
    disablingNode = this.getCertificateValidationControllingValue()
  }

  override string getFramework() { result = "HTTPClient" }
}

/** A configuration to track values that can disable certificate validation for HttpClient. */
private class HttpClientDisablesCertificateValidationConfiguration extends DataFlowImplForHttpClientLibraries::Configuration
{
  HttpClientDisablesCertificateValidationConfiguration() {
    this = "HttpClientDisablesCertificateValidationConfiguration"
  }

  override predicate isSource(DataFlow::Node source) {
    source = DataFlow::getConstant("OpenSSL").getConstant("SSL").getConstant("VERIFY_NONE")
  }

  override predicate isSink(DataFlow::Node sink) {
    sink = any(HttpClientRequest req).getCertificateValidationControllingValue()
  }
}
