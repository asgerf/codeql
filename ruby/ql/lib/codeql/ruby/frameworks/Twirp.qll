/**
 * Provides classes for modeling the `Twirp` framework.
 */

private import codeql.ruby.DataFlow
private import codeql.ruby.CFG
private import codeql.ruby.AST as Ast
private import codeql.ruby.security.ServerSideRequestForgeryCustomizations
private import codeql.ruby.Concepts

/**
 * Provides classes for modeling the `Twirp` framework.
 */
module Twirp {
  /**
   * A Twirp service instantiation
   */
  class ServiceInstantiation extends DataFlow::CallNode {
    ServiceInstantiation() {
      this = DataFlow::getConstant("Twirp").getConstant("Service").getAMethodCall("new")
    }

    private DataFlow::ModuleNode getHandlerClass() {
      result.getAnInstanceReference().flowsTo(this.getArgument(0))
    }

    /**
     * Gets a handler's method.
     */
    Ast::Method getAHandlerMethod() {
      result = this.getHandlerClass().getAnInstanceMethod().asCallableAstNode()
    }
  }

  /**
   * A Twirp client
   */
  class ClientInstantiation extends DataFlow::CallNode {
    ClientInstantiation() {
      this = DataFlow::getConstant("Twirp").getConstant("Client").getAMethodCall("new")
    }
  }

  /** The URL of a Twirp service, considered as a sink. */
  class ServiceUrlAsSsrfSink extends ServerSideRequestForgery::Sink {
    ServiceUrlAsSsrfSink() { exists(ClientInstantiation c | c.getArgument(0) = this) }
  }

  /** A parameter that will receive parts of the url when handling an incoming request. */
  class UnmarshaledParameter extends Http::Server::RequestInputAccess::Range,
    DataFlow::ParameterNode
  {
    UnmarshaledParameter() {
      exists(ServiceInstantiation i | i.getAHandlerMethod().getParameter(0) = this.asParameter())
    }

    override string getSourceType() { result = "Twirp Unmarhaled Parameter" }

    override Http::Server::RequestInputKind getKind() { result = Http::Server::bodyInputKind() }
  }
}
