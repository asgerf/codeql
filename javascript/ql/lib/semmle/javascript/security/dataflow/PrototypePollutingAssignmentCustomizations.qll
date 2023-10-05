/**
 * Provides sources, sinks, and sanitizers for reasoning about assignments
 * that my cause prototype pollution.
 */

private import javascript

/**
 * Provides sources, sinks, and sanitizers for reasoning about assignments
 * that my cause prototype pollution.
 */
module PrototypePollutingAssignment {
  /**
   * A data flow source for untrusted data from which the special `__proto__` property name may be arise.
   */
  abstract class Source extends DataFlow::Node {
    /**
     * Gets a string that describes the type of source.
     */
    abstract string describe();
  }

  /**
   * A data flow sink for prototype-polluting assignments or untrusted property names.
   */
  abstract class Sink extends DataFlow::Node {
    /**
     * Gets the flow label relevant for this sink.
     *
     * Use the `taint` label for untrusted property names, and the `ObjectPrototype` label for
     * object mutations.
     */
    abstract DataFlow::FlowLabel getAFlowLabel();
  }

  /**
   * A sanitizer for untrusted property names.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A barrier guard for prototype-polluting assignments.
   */
  abstract class BarrierGuard extends DataFlow::Node {
    /**
     * Holds if this node acts as a barrier for data flow, blocking further flow from `e` if `this` evaluates to `outcome`.
     */
    predicate blocksExpr(boolean outcome, Expr e) { none() }

    /**
     * Holds if this node acts as a barrier for `label`, blocking further flow from `e` if `this` evaluates to `outcome`.
     */
    predicate blocksExpr(boolean outcome, Expr e, DataFlow::FlowLabel label) { none() }
  }

  /** A subclass of `BarrierGuard` that is used for backward compatibility with the old data flow library. */
  abstract class BarrierGuardLegacy extends BarrierGuard, TaintTracking::SanitizerGuardNode {
    override predicate sanitizes(boolean outcome, Expr e) { this.blocksExpr(outcome, e) }

    override predicate sanitizes(boolean outcome, Expr e, DataFlow::FlowLabel label) {
      this.blocksExpr(outcome, e, label)
    }
  }

  /** A flow label representing the `Object.prototype` value. */
  abstract class ObjectPrototype extends DataFlow::FlowLabel {
    ObjectPrototype() { this = "Object.prototype" }
  }

  /** The base of an assignment or extend call, as a sink for `Object.prototype` references. */
  private class DefaultSink extends Sink {
    DefaultSink() {
      // Avoid using PropWrite here as we only want assignments that can mutate a pre-existing object,
      // so not object literals or array literals.
      this = any(AssignExpr assign).getTarget().(PropAccess).getBase().flow()
      or
      this = any(ExtendCall c).getDestinationOperand()
      or
      this = any(DeleteExpr del).getOperand().flow().(DataFlow::PropRef).getBase()
    }

    override DataFlow::FlowLabel getAFlowLabel() { result instanceof ObjectPrototype }
  }

  /** A remote flow source or location.{hash,search} as a taint source. */
  private class DefaultSource extends Source instanceof RemoteFlowSource {
    override string describe() { result = "user controlled input" }
  }

  import semmle.javascript.PackageExports as Exports

  /**
   * A parameter of an exported function, seen as a source prototype-polluting assignment.
   */
  class ExternalInputSource extends Source {
    ExternalInputSource() {
      this = Exports::getALibraryInputParameter() and not this instanceof RemoteFlowSource
    }

    override string describe() { result = "library input" }
  }
}
