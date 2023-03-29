/**
 * Provides modeling for the `ActiveResource` library.
 * Version: 6.0.0.
 */

private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.controlflow.CfgNodes
private import codeql.ruby.DataFlow
private import codeql.ruby.ApiGraphs

/**
 * Provides modeling for the `ActiveResource` library.
 * Version: 6.0.0.
 */
module ActiveResource {
  /**
   * An ActiveResource class.
   *
   * ```rb
   * class Person < ActiveResource::Base
   * end
   * ```
   */
  class ModelClassNode extends DataFlow::ClassNode {
    ModelClassNode() {
      this = DataFlow::getConstant("ActiveResource").getConstant("Base").getADescendentModule()
    }

    /** Gets a call to `site=`, which sets the base URL for this model. */
    SiteAssignCall getASiteAssignment() { result.getModelClass() = this }

    /** Holds if `c` sets a base URL which does not use HTTPS. */
    predicate disablesCertificateValidation(SiteAssignCall c) {
      c = this.getASiteAssignment() and
      c.disablesCertificateValidation()
    }
  }

  /**
   * DEPRECATED. Use `ModelClassNode` instead.
   */
  deprecated class ModelClass extends ClassDeclaration {
    private ModelClassNode cls;

    ModelClass() { this = cls.getADeclaration() }

    /** DEPRECATED. DO NO USE. */
    deprecated API::Node getModelApiNode() { none() }

    /** Gets a call to `site=`, which sets the base URL for this model. */
    SiteAssignCall getASiteAssignment() { result = cls.getASiteAssignment() }

    /** Holds if `c` sets a base URL which does not use HTTPS. */
    predicate disablesCertificateValidation(SiteAssignCall c) {
      cls.disablesCertificateValidation(c)
    }
  }

  /**
   * DEPRECATED. Use `getAMethodCall`
   * A call to a class method on an ActiveResource model class.
   *
   * ```rb
   * class Person < ActiveResource::Base
   * end
   *
   * Person.find(1)
   * ```
   */
  class ModelClassMethodCall extends DataFlow::CallNode {
    ModelClassNode model;

    ModelClassMethodCall() { this = model.getAModuleCall(_) }

    /** Gets the model class for this call. */
    ModelClassNode getModelClass() { result = model }
  }

  /**
   * A call to `site=` on an ActiveResource model class.
   * This sets the base URL for all HTTP requests made by this class.
   */
  private class SiteAssignCall extends ModelClassMethodCall {
    SiteAssignCall() { this.getMethodName() = "site=" }

    /**
     * Gets a node that contributes to the URLs used for HTTP requests by the parent
     * class.
     */
    DataFlow::Node getAUrlPart() { result = this.getArgument(0) }

    /** Holds if this site value specifies HTTP rather than HTTPS. */
    predicate disablesCertificateValidation() {
      this.getAUrlPart()
          .asExpr()
          .(ExprNodes::AssignExprCfgNode)
          .getRhs()
          .getConstantValue()
          .getString()
          .regexpMatch("^http[^s].+")
    }
  }

  /**
   * A call to the `find` class method, which returns an ActiveResource model
   * object.
   *
   * ```rb
   * alice = Person.find(1)
   * ```
   */
  class FindCall extends ModelClassMethodCall {
    FindCall() { this.getMethodName() = "find" }
  }

  /**
   * A call to the `create(!)` class method, which returns an ActiveResource model
   * object.
   *
   * ```rb
   * alice = Person.create(name: "alice")
   * ```
   */
  class CreateCall extends ModelClassMethodCall {
    CreateCall() { this.getMethodName() = ["create", "create!"] }
  }

  /**
   * A call to a method that sends a custom HTTP request outside of the
   * ActiveResource conventions. This typically returns an ActiveResource model
   * object. It may return a collection, but we don't currently model that.
   *
   * ```rb
   * alice = Person.get(:active)
   * ```
   */
  class CustomHttpCall extends ModelClassMethodCall {
    CustomHttpCall() { this.getMethodName() = ["get", "post", "put", "patch", "delete"] }
  }

  /**
   * An ActiveResource model object.
   */
  class ModelInstance extends DataFlow::LocalSourceNode {
    ModelClassNode cls;

    ModelInstance() {
      this = cls.getAnOwnInstanceSelf()
      or
      this.(ModelClassMethodCall).getModelClass() = cls and
      (this instanceof FindCall or this instanceof CreateCall or this instanceof CustomHttpCall)
    }

    /** Gets the model class for this instance. */
    ModelClassNode getModelClass() { result = cls }
  }

  /**
   * A call to a method on an ActiveResource model object.
   */
  class ModelInstanceMethodCall extends DataFlow::CallNode {
    ModelInstance instance;

    ModelInstanceMethodCall() { this = instance.getAMethodCall() }

    /** Gets the model instance for this call. */
    ModelInstance getInstance() { result = instance }

    /** Gets the model class for this call. */
    ModelClassNode getModelClass() { result = instance.getModelClass() }
  }

  /**
   * A call that returns a collection of ActiveResource model objects.
   */
  class Collection extends ModelClassMethodCall {
    Collection() {
      this.getMethodName() = "all"
      or
      this.getMethodName() = "find" and
      this.getArgument(0).getConstantValue().isStringlikeValue("all")
    }
  }

  /**
   * A method call on a collection.
   */
  class CollectionCall extends DataFlow::CallNode {
    private Collection collection;

    CollectionCall() { this = collection.getAMethodCall() }

    /** Gets the collection for this call. */
    Collection getCollection() { result = collection }
  }

  private class ModelClassMethodCallAsHttpRequest extends Http::Client::Request::Range,
    ModelClassMethodCall
  {
    ModelClassMethodCallAsHttpRequest() {
      this.getMethodName() = ["all", "build", "create", "create!", "find", "first", "last"]
    }

    override string getFramework() { result = "ActiveResource" }

    override predicate disablesCertificateValidation(
      DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
    ) {
      this.getModelClass().disablesCertificateValidation(disablingNode) and
      // TODO: highlight real argument origin
      argumentOrigin = disablingNode
    }

    override DataFlow::Node getAUrlPart() {
      result = this.getModelClass().getASiteAssignment().getAUrlPart()
    }

    override DataFlow::Node getResponseBody() { result = this }
  }

  private class ModelInstanceMethodCallAsHttpRequest extends Http::Client::Request::Range,
    ModelInstanceMethodCall
  {
    ModelInstanceMethodCallAsHttpRequest() {
      this.getMethodName() =
        [
          "exists?", "reload", "save", "save!", "destroy", "delete", "get", "patch", "post", "put",
          "update_attribute", "update_attributes"
        ]
    }

    override string getFramework() { result = "ActiveResource" }

    override predicate disablesCertificateValidation(
      DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
    ) {
      this.getModelClass().disablesCertificateValidation(disablingNode) and
      // TODO: highlight real argument origin
      argumentOrigin = disablingNode
    }

    override DataFlow::Node getAUrlPart() {
      result = this.getModelClass().getASiteAssignment().getAUrlPart()
    }

    override DataFlow::Node getResponseBody() { result = this }
  }
}
