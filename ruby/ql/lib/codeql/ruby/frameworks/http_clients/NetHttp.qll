/**
 * Provides modeling for the `Net::HTTP` library.
 */

private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.dataflow.RemoteFlowSources
private import codeql.ruby.dataflow.internal.DataFlowPublic
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowImplForHttpClientLibraries as DataFlowImplForHttpClientLibraries

/**
 * A `Net::HTTP` call which initiates an HTTP request.
 * ```ruby
 * Net::HTTP.get("http://example.com/")
 * Net::HTTP.post("http://example.com/", "some_data")
 * req = Net::HTTP.new("example.com")
 * response = req.get("/")
 * ```
 */
class NetHttpRequest extends Http::Client::Request::Range, DataFlow::CallNode {
  private boolean isBodyReturned;

  NetHttpRequest() {
    // Net::HTTP.get(...)
    this = DataFlow::getConstant("Net").getConstant("HTTP").getAMethodCall("get") and
    isBodyReturned = true
    or
    // Net::HTTP.post(...).body
    this = DataFlow::getConstant("Net").getConstant("HTTP").getAMethodCall(["post", "post_form"]) and
    isBodyReturned = false
    or
    // Net::HTTP.new(..).get(..).body
    this =
      DataFlow::getConstant("Net")
          .getConstant("HTTP")
          .getAMethodCall("new")
          .getAMethodCall([
              "get", "get2", "request_get", "head", "head2", "request_head", "delete", "put",
              "patch", "post", "post2", "request_post", "request"
            ]) and
    isBodyReturned = false
  }

  /**
   * Gets a node that contributes to the URL of the request.
   */
  override DataFlow::Node getAUrlPart() {
    result = this.getArgument(0)
    or
    // Net::HTTP.new(...).get(...)
    exists(DataFlow::CallNode new |
      new = DataFlow::getConstant("Net").getConstant("HTTP").getAMethodCall("new") and
      this = new.getAMethodCall(_)
    |
      result = new.getArgument(0)
    )
  }

  override DataFlow::Node getResponseBody() {
    if isBodyReturned = true
    then result = this
    else result = this.getAMethodCall(["body", "read_body", "entity"])
  }

  /** Gets the value that controls certificate validation, if any. */
  DataFlow::Node getCertificateValidationControllingValue() {
    // A Net::HTTP request bypasses certificate validation if we see a setter
    // call like this:
    //   foo.verify_mode = OpenSSL::SSL::VERIFY_NONE
    // and then the receiver of that call flows to the receiver in the request:
    //   foo.request(...)
    exists(DataFlow::CallNode setter |
      setter.asExpr().getExpr().(SetterMethodCall).getMethodName() = "verify_mode=" and
      result = setter.getArgument(0) and
      localFlow(setter.getReceiver(), this.getReceiver())
    )
  }

  cached
  override predicate disablesCertificateValidation(
    DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
  ) {
    any(NetHttpDisablesCertificateValidationConfiguration config)
        .hasFlow(argumentOrigin, disablingNode) and
    disablingNode = this.getCertificateValidationControllingValue()
  }

  override string getFramework() { result = "Net::HTTP" }
}

/** A configuration to track values that can disable certificate validation for NetHttp. */
private class NetHttpDisablesCertificateValidationConfiguration extends DataFlowImplForHttpClientLibraries::Configuration
{
  NetHttpDisablesCertificateValidationConfiguration() {
    this = "NetHttpDisablesCertificateValidationConfiguration"
  }

  override predicate isSource(DataFlow::Node source) {
    source = DataFlow::getConstant("OpenSSL").getConstant("SSL").getConstant("VERIFY_NONE")
  }

  override predicate isSink(DataFlow::Node sink) {
    sink = any(NetHttpRequest req).getCertificateValidationControllingValue()
  }
}
