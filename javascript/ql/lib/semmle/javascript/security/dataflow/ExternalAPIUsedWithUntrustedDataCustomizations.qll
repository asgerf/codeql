/**
 * Provides sources, sinks and sanitizers for reasoning about flow of
 * untrusted data into an external API.
 */

import javascript
private import semmle.javascript.FuzzyModels

/**
 * Provides sources, sinks and sanitizers for reasoning about flow of
 * untrusted data into an external API.
 */
module ExternalApiUsedWithUntrustedData {
  /**
   * A source of untrusted data.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * An input to an external API call.
   */
  abstract class Sink extends DataFlow::Node {
    /**
     * Gets a human-readable name for the external API which this value flows into.
     *
     * This has the form of a pseudo-access path leading to the sink. Some ambiguity
     * is tolerated in exchange for better readability here, as the user will typically
     * have to scan over many irrelevant sinks in order to pick out the interesting ones.
     */
    abstract string getApiName();
  }

  /**
   * A value that is treated as a generic deep object sink.
   *
   * By default, this includes the objects passed to a `PropertyProjection` or `ExtendCall`.
   *
   * Such objects tend to have lots of application-defined properties which don't represent
   * distinct API usages, so the query will avoid generating API names from them.
   */
  abstract class DeepObjectSink extends DataFlow::Node { }

  private class DefaultDeepObjectSink extends DeepObjectSink {
    DefaultDeepObjectSink() {
      this = any(PropertyProjection p).getObject()
      or
      this = any(ExtendCall c).getAnOperand()
    }
  }

  /** Holds if `node` corresponds to a deep object argument. */
  private predicate isDeepObjectSink(API::Node node) { node.asSink() instanceof DeepObjectSink }

  /**
   * A sanitizer for data flowing to an external API.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  private class RemoteFlowAsSource extends Source instanceof RemoteFlowSource { }

  /**
   * A package name whose entire API is considered "safe" for the purpose of this query.
   */
  abstract class SafeExternalApiPackage extends string {
    SafeExternalApiPackage() { exists(API::moduleImport(this)) }
  }

  private class DefaultSafeExternalApiPackage extends SafeExternalApiPackage {
    DefaultSafeExternalApiPackage() {
      // Promise libraries are safe and generate too much noise if included
      this =
        [
          "bluebird", "q", "deferred", "when", "promise", "promises", "es6-promise",
          "promise-polyfill"
        ]
    }
  }

  /**
   * A function that is considered a "safe" external API from a security perspective.
   */
  abstract class SafeExternalApiFunction extends API::Node { }

  /**
   * A call to an external API.
   */
  private class ExternalApiInvocation extends DataFlow::InvokeNode {
    private string packageName;
    private string methodName;

    ExternalApiInvocation() {
      this = externalCall(packageName, methodName) and
      not this = any(SafeExternalApiFunction f).getACall() and
      not packageName instanceof SafeExternalApiPackage
    }

    /** Gets the API name representing this call. */
    string getApiName() { result = packageName + "." + methodName }
  }

  /**
   * Holds if `object` can be seen as a record of named arguments to a call.
   *
   * This holds for all object literals except deep object sinks.
   */
  private predicate isNamedArgumentObject(DataFlow::ObjectLiteralNode object) {
    not object instanceof DeepObjectSink
  }

  /** An argument to an external API call, seen as a sink. */
  private class DirectParameterSink extends Sink {
    ExternalApiInvocation invoke;
    int index;

    DirectParameterSink() {
      this = invoke.getArgument(index) and
      not isNamedArgumentObject(this) // handled by NamedParameterSink
      or
      this = invoke.getArgument(index).(DataFlow::ObjectLiteralNode).getASpreadProperty()
    }

    override string getApiName() { result = invoke.getApiName() + " Argument[" + index + "]" }
  }

  /** A spread argument or an unknown-index argument to an external API. */
  private class SpreadParameterSink extends Sink {
    ExternalApiInvocation invoke;

    SpreadParameterSink() {
      this = invoke.getASpreadArgument()
      or
      exists(InvokeExpr expr, int i | expr = invoke.asExpr() |
        this = expr.getArgument(i).flow() and
        expr.getArgument([0 .. i - 1]) instanceof SpreadElement
      )
    }

    override string getApiName() { result = invoke.getApiName() + " Argument[0..]" }
  }

  /** A "named argument" to an external API call, seen as a sink. */
  private class NamedParameterSink extends Sink {
    ExternalApiInvocation invoke;
    int index;
    string prop;

    NamedParameterSink() {
      exists(DataFlow::ObjectLiteralNode object, DataFlow::PropWrite write |
        object = invoke.getArgument(index) and
        isNamedArgumentObject(object) and
        write = object.getAPropertyWrite() and
        this = write.getRhs() and
        (
          prop = write.getPropertyName()
          or
          not exists(write.getPropertyName()) and
          prop = "*"
        )
      )
    }

    override string getApiName() {
      result = invoke.getApiName() + " Argument[" + index + "].Member[" + prop + "]"
    }
  }

  /** The return value from a direct callback to an external API call, seen as a sink */
  private class CallbackSink extends Sink {
    ExternalApiInvocation invoke;
    int index;

    CallbackSink() {
      this = invoke.getCallback(index).getAReturn() and
      // Exclude promise-related method names for callback-return sinks
      not invoke.getCalleeName() = ["then", "catch", "finally"]
    }

    override string getApiName() {
      result = invoke.getApiName() + " Argument[" + index + "].ReturnValue"
    }
  }

  /** The return value from a named callback to an external API call, seen as a sink. */
  private class NamedCallbackSink extends Sink {
    ExternalApiInvocation invoke;
    int index;
    string prop;

    NamedCallbackSink() {
      this =
        invoke
            .getOptionArgument(index, prop)
            .getALocalSource()
            .(DataFlow::FunctionNode)
            .getAReturn()
    }

    override string getApiName() {
      result = invoke.getApiName() + " Argument[" + index + "].Member[" + prop + "].ReturnValue"
    }
  }
}
