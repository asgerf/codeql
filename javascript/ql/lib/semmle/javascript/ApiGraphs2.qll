import javascript
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import internal.CachedStages
private import semmle.javascript.DeepFlow
private import semmle.javascript.dataflow.internal.DataFlowNode

module API2 {
  deprecated Node root() { none() }

  /**
   * A class for contributing new steps for tracking uses of an API.
   */
  class AdditionalUseStep extends Unit {
    /**
     * Holds if use nodes should flow from `pred` to `succ`.
     */
    predicate step(DataFlow::SourceNode pred, DataFlow::SourceNode succ) { none() }
  }

  private module AdditionalUseStep {
    pragma[nomagic]
    predicate step(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
      any(AdditionalUseStep st).step(pred, succ)
    }
  }

  cached
  Node moduleImport(string name) {
    result = DataFlow::moduleImport(name)
    or
    result = DataFlow::moduleMember(name, "default")
  }

  module Node {
    Node ofType(string packageName, string typeName) {
      result.(DataFlow::SourceNode).hasUnderlyingType(packageName, typeName)
    }
  }

  class InvokeNode extends DataFlow::InvokeNode {
    pragma[inline]
    SinkNode getParameter(int i) { result = this.getArgument(i) }

    pragma[inline]
    SinkNode getAParameter() { result = this.getAnArgument() }

    pragma[inline]
    SinkNode getLastParameter() { result = this.getLastArgument() }

    pragma[inline]
    Node getReturn() { result = this }

    pragma[inline]
    Node getInstance() { result = this and this instanceof DataFlow::NewNode }
  }

  class CallNode extends InvokeNode, DataFlow::CallNode { }

  class NewNode extends InvokeNode, DataFlow::NewNode { }

  class Node extends TNode instanceof DataFlow::SourceNode {
    deprecated Node getASuccessor() { none() }

    string toString() { result = super.toString() }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      super.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    pragma[inline]
    private DataFlow::SourceNode forward() {
      Deep::hasFlowTo(pragma[only_bind_out](this), pragma[only_bind_into](result))
    }

    pragma[inline]
    DataFlow::Node getAValueReachableFromSource() { result = this.forward().getALocalUse() }

    pragma[inline]
    DataFlow::SourceNode asSource() { result = this }

    pragma[inline]
    API2::CallNode getACall() { result = this.forward().getACall() }

    pragma[inline]
    API2::CallNode getMaybePromisifiedCall() {
      result = this.getACall()
      or
      result = Deep::getABoundInvocation(this, true, _)
    }

    pragma[inline]
    API2::NewNode getAnInstantiation() { result = this.forward().getAnInstantiation() }

    pragma[inline]
    API2::InvokeNode getAnInvocation() { result = this.forward().getAnInvocation() }

    pragma[inline]
    API2::Node getMember(string name) { result = Deep::getLoad(pragma[only_bind_out](this), name) }

    pragma[inline]
    API2::Node getUnknownMember() {
      DataFlow::SourceNode::Internal::dynamicPropRef(pragma[only_bind_out](this).forward(),
        pragma[only_bind_into](result)) and
      pragma[only_bind_out](result) instanceof DataFlow::PropRead
      // Note: The type check above is not strictly needed since API::Node is a subtype of SourceNode, and PropWrite is not a SourceNode.
      // TODO: Investigate which check is more efficient in practice.
    }

    pragma[inline]
    API2::Node getAMember() { result = pragma[only_bind_out](this.forward()).getAPropertyRead() }

    pragma[inline]
    API2::Node getInstance() {
      result = this.getAnInstantiation() // note: these predicates return the same thing, but with different types
    }

    pragma[inline]
    API2::SinkNode getParameter(int i) {
      Deep::argumentPassing(pragma[only_bind_out](this), i, result)
    }

    pragma[inline]
    API2::SinkNode getLastParameter() {
      result = pragma[only_bind_out](this.getACall()).getLastArgument()
      or
      result =
        TApiSyntheticCallbackArg(Deep::getABoundInvocation(pragma[only_bind_out](this), true, _))
    }

    pragma[inline]
    API2::SinkNode getAParameter() { Deep::argumentPassing(pragma[only_bind_out](this), _, result) }

    pragma[inline]
    API2::SinkNode getReceiver() {
      Deep::receiverPassing(this, result) // TODO: change to only return explicit receivers?
    }

    pragma[inline]
    API2::Node getReturn() {
      result = this.getAnInvocation() // note: these predicates return the same thing, but with different types
    }

    pragma[inline]
    API2::Node getPromised() { result = Deep::getPromised(this) }

    pragma[inline]
    API2::Node getPromisedError() { result = Deep::getPromisedError(this) }

    Node getADecoratedClass() { none() } // TODO

    Node getADecoratedMember() { none() } // TODO

    SinkNode getADecoratedParameter() { none() } // TODO

    /**
     * DEPRECATED. Use `getACall().getNumArgument()` instead, but note that each call may have a different number of arguments.
     *
     * This predicate returns the largest arity among these calls, or zero if there are no calls.
     */
    deprecated int getNumParameter() { result = max(int s | exists(this.getParameter(s))) + 1 }

    /** DEPRECATED. `API::Node` can no longer represent sinks -- use `API::SinkNode` instead. */
    deprecated DataFlow::Node asSink() { none() }

    /** DEPRECATED. `API::Node` can no longer represent sinks -- use `API::SinkNode` instead. */
    deprecated DataFlow::SourceNode getAValueReachingSink() { none() }

    /** DEPRECATED. This predicate has been renamed to `asSource`. */
    deprecated DataFlow::SourceNode getAnImmediateUse() { result = this.asSource() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachableFromSource`. */
    deprecated DataFlow::Node getAUse() { result = this.getAValueReachableFromSource() }

    /** DEPRECATED. This predicate has been renamed to `asSink` and moved to the `API::SinkNode` class. */
    deprecated DataFlow::Node getARhs() { result = this.asSink() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachingSink` and moved to the `API::SinkNode` class. */
    deprecated DataFlow::Node getAValueReachingRhs() { result = this.getAValueReachingSink() }
  }

  class BacktrackingNode extends TNode instanceof DataFlow::SourceNode {
    // TODO: include synth callback arg
    string toString() { result = this.(DataFlow::Node).toString() }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.(DataFlow::Node).hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    pragma[inline]
    private DataFlow::SourceNode backward() {
      Deep::hasFlowTo(pragma[only_bind_into](result), pragma[only_bind_out](this))
    }

    pragma[inline]
    DataFlow::SourceNode getAValueReachingSink() { result = this.backward() }

    pragma[inline]
    DataFlow::FunctionNode getAFunction() { result = this.backward() }

    pragma[inline]
    API2::SinkNode getMember(string name) {
      // TODO: include store edges for class members
      // TODO: include reverse-load edges for stepping through long access paths
      result = this.backward().getAPropertyWrite(name).getRhs()
    }

    pragma[inline]
    API2::SinkNode getUnknownMember() {
      exists(DataFlow::PropWrite write |
        DataFlow::SourceNode::Internal::dynamicPropRef(pragma[only_bind_out](this).backward(),
          pragma[only_bind_into](write)) and
        result = write.getRhs()
      )
    }

    pragma[inline]
    API2::SinkNode getAMember() {
      // TODO: include store edges for class members
      result = this.backward().getAPropertyWrite().getRhs()
    }

    pragma[inline]
    API2::Node getInstance() { result = Deep::getClassReceiverRef(this.backward()) }

    pragma[inline]
    API2::Node getParameter(int i) { Deep::parameterDef(this.backward(), i, result) }

    pragma[inline]
    API2::Node getAParameter() { Deep::parameterDef(this.backward(), _, result) }

    pragma[inline]
    API2::Node getLastParameter() {
      // TODO: is this the best way to do this?
      exists(DataFlow::SourceNode src | src = this.backward() |
        result = src.(DataFlow::FunctionNode).getLastParameter()
        or
        result = src.(DataFlow::ClassNode).getConstructor().getLastParameter()
      )
    }

    pragma[inline]
    API2::Node getReceiver() { result = this.getAFunction().getReceiver() }

    pragma[inline]
    API2::SinkNode getReturn() { result = Deep::getPrettyReturn(this.getAFunction()) }

    pragma[inline]
    API2::SinkNode getPromised() {
      result = Deep::getStoreRhs(this.backward(), Promises::valueProp())
    }

    pragma[inline]
    API2::SinkNode getPromisedError() {
      result = Deep::getStoreRhs(this.backward(), Promises::errorProp())
    }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated API::Node getADecoratedClass() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated API::Node getADecoratedMember() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated API::Node getADecoratedParameter() { none() }

    /**
     * DEPRECATED. Use `getAFunction().getNumParameter()` instad, but note that different functions flowing here may
     * each have a different number of parameters.
     *
     * This predicate returns the largest number of parameters, or zero if there are no functions flowing here.
     */
    deprecated int getNumParameter() { result = max(int s | exists(this.getParameter(s))) + 1 }

    /**
     * DEPRECATED. This predicate should only be used on `API::SinkNode`. Once backtracking is performed the node is rarely
     * useful as a sink.
     *
     * Returns the receiver itself as a data-flow node, though this does not generally have the appropriate location for u
     */
    deprecated DataFlow::Node asSink() { result = this }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::CallNode getAnInvocation() { none() }

    /**
     * DEPRECATED. This predicate has no result for backtracking nodes.
     * - For finding references to `this` inside a class, use `getInstance()` instead.
     * - For finding instantiation sites of a class, use a forward-tracking node instead (`API::Node`).
     */
    deprecated DataFlow::NewNode getAnInstantiation() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::CallNode getACall() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::CallNode getMaybePromisifiedCall() { none() }

    /** DEPRECATED. This predicate has been renamed to `asSource` and is only usable for forward-tracking nodes (`API::Node`). */
    deprecated DataFlow::SourceNode getAnImmediateUse() { none() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachableFromSource` and is only usable for forward-tracking nodes (`API::Node`). */
    deprecated DataFlow::Node getAUse() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::SourceNode asSource() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::SourceNode getAValueReachableFromSource() { none() }

    /** DEPRECATED. This predicate has been renamed to `asSink` and should only be use on the `API::SinkNode` class. */
    deprecated DataFlow::Node getARhs() { result = this.asSink() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachingSink`. */
    deprecated DataFlow::Node getAValueReachingRhs() { result = this.getAValueReachingSink() }
  }

  class SinkNode extends TDataFlowNodeOrApiNode {
    // TODO: include synth callback arg
    string toString() { result = this.(DataFlow::Node).toString() }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.(DataFlow::Node).hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    pragma[inline]
    API2::BacktrackingNode backtrack() {
      result = pragma[only_bind_out](this).(DataFlow::Node).getALocalSource()
    }

    pragma[inline]
    DataFlow::SourceNode getAValueReachingSink() {
      result = this.backtrack().getAValueReachingSink()
    }

    pragma[inline]
    API2::SinkNode getMember(string name) { result = this.backtrack().getMember(name) }

    pragma[inline]
    API2::SinkNode getUnknownMember() { result = this.backtrack().getUnknownMember() }

    pragma[inline]
    API2::SinkNode getAMember() { result = this.backtrack().getAMember() }

    pragma[inline]
    API2::Node getInstance() { result = this.backtrack().getInstance() }

    pragma[inline]
    API2::Node getParameter(int i) {
      result = this.backtrack().getParameter(i)
      or
      Deep::promisifiedCallbackParameterDef(this, i, result)
    }

    pragma[inline]
    API2::Node getAParameter() { result = this.backtrack().getAParameter() }

    pragma[inline]
    API2::Node getLastParameter() { result = this.backtrack().getLastParameter() }

    pragma[inline]
    API2::Node getReceiver() { result = this.backtrack().getReceiver() }

    pragma[inline]
    API2::SinkNode getReturn() { result = this.backtrack().getReturn() }

    pragma[inline]
    API2::SinkNode getPromised() { result = this.backtrack().getPromised() }

    pragma[inline]
    API2::SinkNode getPromisedError() { result = this.backtrack().getPromisedError() }

    /**
     * Returns this node as a data-flow node.
     */
    pragma[inline]
    DataFlow::Node asSink() { result = this }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated API::Node getADecoratedClass() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated API::Node getADecoratedMember() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated API::Node getADecoratedParameter() { none() }

    /**
     * DEPRECATED. Use `getAFunction().getNumParameter()` instad, but note that different functions flowing here may
     * each have a different number of parameters.
     *
     * This predicate returns the largest number of parameters, or zero if there are no functions flowing here.
     */
    deprecated int getNumParameter() { result = max(int s | exists(this.getParameter(s))) + 1 }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::CallNode getAnInvocation() { none() }

    /**
     * DEPRECATED. This predicate has no result for backtracking nodes.
     * - For finding references to `this` inside a class, use `getInstance()` instead.
     * - For finding instantiation sites of a class, use a forward-tracking node instead (`API::Node`).
     */
    deprecated DataFlow::NewNode getAnInstantiation() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::CallNode getACall() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::CallNode getMaybePromisifiedCall() { none() }

    /** DEPRECATED. This predicate has been renamed to `asSource` and is only usable for forward-tracking nodes (`API::Node`). */
    deprecated DataFlow::SourceNode getAnImmediateUse() { none() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachableFromSource` and is only usable for forward-tracking nodes (`API::Node`). */
    deprecated DataFlow::Node getAUse() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::SourceNode asSource() { none() }

    /** DEPRECATED. This predicate has no result for backtracking nodes, use a forward-tracking node instead (`API::Node`). */
    deprecated DataFlow::SourceNode getAValueReachableFromSource() { none() }

    /** DEPRECATED. This predicate has been renamed to `asSink` and should only be use on the `API::SinkNode` class. */
    deprecated DataFlow::Node getARhs() { result = this.asSink() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachingSink`. */
    deprecated DataFlow::Node getAValueReachingRhs() { result = this.getAValueReachingSink() }
  }
}
