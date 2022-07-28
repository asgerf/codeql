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

  class Node extends TDataFlowNode instanceof DataFlow::SourceNode {
    deprecated DataFlow::Node getInducingNode() { result = this }

    deprecated int getDepth() { result = 0 } // TODO

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
        TApiNode_PromisifiedCallbackNode(Deep::getABoundInvocation(pragma[only_bind_out](this),
            true, _))
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

  class SinkNode extends TDataFlowNodeOrApiNode {
    string toString() {
      result = this.(DataFlow::Node).toString()
      or
      result = this.(Internal::PromisifiedCallbackNode).toString()
    }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.(DataFlow::Node).hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
      or
      this.(Internal::PromisifiedCallbackNode)
          .hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    pragma[inline]
    private DataFlow::SourceNode backward() {
      exists(DataFlow::SourceNode localSource |
        localSource = pragma[only_bind_out](this).(DataFlow::Node).getALocalSource() and
        Deep::hasFlowTo(pragma[only_bind_into](result), pragma[only_bind_out](localSource))
      )
    }

    pragma[inline]
    DataFlow::SourceNode getAValueReachingSink() { result = this.backward() }

    pragma[inline]
    API2::SinkNode getMember(string name) {
      // TODO: include store edges for class members
      // TODO: include reverse-load edges for stepping through long access paths
      result = Deep::getStoreRhs(this.backward(), name) //prop) this.backward().getAPropertyWrite(name).getRhs()
      or
      exists(DataFlow::ClassNode cls |
        this.backward() = cls.getConstructor().getReceiver() and
        result = cls.getInstanceMethod(name)
      )
    }

    pragma[inline]
    API2::SinkNode getUnknownMember() {
      exists(DataFlow::PropWrite write |
        DataFlow::SourceNode::Internal::dynamicPropRef(this.backward(),
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
    API2::SinkNode getInstance() { result = Deep::getClassReceiverRef(this.backward()) }

    pragma[inline]
    API2::Node getParameter(int i) {
      Deep::parameterDef(this.backward(), i, result)
      or
      Deep::promisifiedCallbackParameterDef(pragma[only_bind_out](this), i, result)
    }

    pragma[inline]
    API2::Node getAParameter() {
      Deep::parameterDef(this.backward(), _, result)
      or
      Deep::promisifiedCallbackParameterDef(pragma[only_bind_out](this), _, result)
    }

    pragma[inline]
    API2::Node getLastParameter() {
      // TODO: is this the best way to do this?
      exists(DataFlow::SourceNode src | src = this.backward() |
        result = src.(DataFlow::FunctionNode).getLastParameter()
        or
        result = src.(DataFlow::ClassNode).getConstructor().getLastParameter()
      )
      or
      Deep::promisifiedCallbackParameterDef(pragma[only_bind_out](this), 1, result)
    }

    pragma[inline]
    API2::Node getReceiver() { result = this.backward().(DataFlow::FunctionNode).getReceiver() }

    pragma[inline]
    API2::SinkNode getReturn() { result = Deep::getPrettyReturn(this.backward()) }

    pragma[inline]
    API2::SinkNode getPromised() {
      result = Deep::getStoreRhs(this.backward(), Promises::valueProp())
    }

    pragma[inline]
    API2::SinkNode getPromisedError() {
      result = Deep::getStoreRhs(this.backward(), Promises::errorProp())
    }

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

  /** Internal classes */
  module Internal {
    /**
     * An API node representing a callback passed to a promisified version of a function.
     *
     * At every call to a promisified function, this node represents the callback passed on to the
     * original function. The callback parameters flow to the point where the returned promise
     * is consumed by an `await` or similar.
     */
    class PromisifiedCallbackNode extends TApiNode_PromisifiedCallbackNode {
      string toString() { result = "synthetic callback from promisification" }

      predicate hasLocationInfo(
        string filepath, int startline, int startcolumn, int endline, int endcolumn
      ) {
        exists(DataFlow::CallNode call |
          this = TApiNode_PromisifiedCallbackNode(call) and
          call.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
        )
      }
    }
  }

  class GraphNode = Graph::GraphNode;

  module Graph = GraphInternal;
}

private module GraphInternal {
  private newtype TGraphNode =
    MkRoot() or
    MkUse(API2::Node node) or
    MkDef(API2::SinkNode node) { isDef(node) }

  GraphNode root() { result = MkRoot() }

  private predicate isDef(API2::SinkNode node) {
    node = any(DataFlow::InvokeNode invoke).getAnArgument()
    or
    node = any(DataFlow::PropWrite write).getRhs()
    or
    node = Deep::getPrettyReturn(_)
    or
    node instanceof API::Internal::PromisifiedCallbackNode
    or
    node = any(DataFlow::ClassNode c).getAReceiverNode() // relevant if class escapes
  }

  class GraphNode extends TGraphNode {
    API2::Node asUseNode() { this = MkUse(result) }

    API2::SinkNode asDefNode() { this = MkDef(result) }

    string toString() {
      this = MkRoot() and result = "root"
      or
      this instanceof MkUse and
      result = "use " + this.getPath()
      or
      this instanceof MkDef and
      result = "def " + this.getPath()
    }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.asUseNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
      or
      this.asDefNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    GraphNode getASuccessor() { edge(this, _, result) }

    GraphNode getASuccessor(Label::ApiLabel label) { edge(this, label, result) }

    private string getAPath(int length) {
      this instanceof MkRoot and
      length = 0 and
      result = ""
      or
      exists(GraphNode pred, Label::ApiLabel lbl, string predpath |
        edge(pred, lbl, this) and
        predpath = pred.getAPath(length - 1) and
        exists(string dot | if length = 1 then dot = "" else dot = "." |
          result = predpath + dot + lbl and
          // avoid producing strings longer than 1MB
          result.length() < 1000 * 1000
        )
      ) and
      length in [1 .. distanceFromRoot(this)]
    }

    string getPath() { result = min(string p | p = this.getAPath(distanceFromRoot(this)) | p) }

    int getDepth() { result = distanceFromRoot(this) }
  }

  private int edgeCount() {
    result =
      strictcount(GraphNode graphPred, Label::ApiLabel label, GraphNode graphSucc |
        edge(graphPred, label, graphSucc)
      )
  }

  private predicate edge(GraphNode graphPred, Label::ApiLabel label, GraphNode graphSucc) {
    // Use -> Use edges
    exists(API2::Node pred, API2::Node succ |
      graphPred.asUseNode() = pred and
      graphSucc.asUseNode() = succ
    |
      exists(string m | pred.getMember(m) = succ and label = Label::member(m))
      or
      pred.getUnknownMember() = succ and label = Label::unknownMember()
      or
      pred.getInstance() = succ and label = Label::instance()
      or
      pred.getReturn() = succ and label = Label::return()
      or
      pred.getPromised() = succ and label = Label::promised()
      or
      pred.getPromisedError() = succ and label = Label::promisedError()
    )
    or
    // Def -> Def edges
    exists(API2::SinkNode pred, API2::SinkNode succ |
      graphPred.asDefNode() = pred and
      graphSucc.asDefNode() = succ
    |
      exists(string m | pred.getMember(m) = succ and label = Label::member(m))
      or
      pred.getUnknownMember() = succ and label = Label::unknownMember()
      or
      pred.getReturn() = succ and label = Label::return()
      or
      pred.getPromised() = succ and label = Label::promised()
      or
      pred.getPromisedError() = succ and label = Label::promisedError()
      or
      pred.getInstance() = succ and label = Label::instance()
    )
    or
    // Def -> Use edges
    exists(API2::SinkNode pred, API2::Node succ |
      graphPred.asDefNode() = pred and
      graphSucc.asUseNode() = succ
    |
      exists(int i | pred.getParameter(i) = succ and label = Label::parameter(i))
      or
      pred.getReceiver() = succ and label = Label::receiver()
    )
    or
    // Use -> Def edges
    exists(API2::Node pred, API2::SinkNode succ |
      graphPred.asUseNode() = pred and
      graphSucc.asDefNode() = succ
    |
      exists(int i | pred.getParameter(i) = succ and label = Label::parameter(i))
      or
      pred.getReceiver() = succ and label = Label::receiver()
    )
    or
    // Root -> Use
    exists(API2::Node succ |
      graphPred = MkRoot() and
      graphSucc.asUseNode() = succ
    |
      exists(string name | succ = API::moduleImport(name) and label = Label::moduleLabel(name))
      or
      exists(string packageName, string typeName |
        succ = API2::Node::ofType(packageName, typeName) and
        label = Label::typeUse(packageName, typeName)
      )
    )
  }

  private predicate edge(GraphNode graphPred, GraphNode graphSucc) { edge(graphPred, _, graphSucc) }

  private int distanceFromRoot(GraphNode node) =
    shortestDistances(MkRoot/0, edge/2)(_, node, result)

  module Label {
    /** A label in the API-graph */
    class ApiLabel extends TLabel {
      /** Gets a string representation of this label. */
      string toString() { result = "???" }
    }

    /** Gets the edge label for the module `m`. */
    LabelModule moduleLabel(string m) { result.getMod() = m }

    /** Gets the `member` edge label for member `m`. */
    bindingset[m]
    bindingset[result]
    LabelMember member(string m) { result.getProperty() = m }

    /** Gets the `type-use` edge label. */
    LabelTypeUse typeUse(string moduleName, string typeName) {
      result.getModuleName() = moduleName and
      result.getTypeName() = typeName
    }

    /** Gets the `member` edge label for the unknown member. */
    LabelUnknownMember unknownMember() { any() }

    /**
     * Gets a property name referred to by the given dynamic property access,
     * allowing one property flow step in the process (to allow flow through imports).
     *
     * This is to support code patterns where the property name is actually constant,
     * but the property name has been factored into a library.
     */
    private string getAnIndirectPropName(DataFlow::PropRef ref) {
      exists(DataFlow::Node pred |
        FlowSteps::propertyFlowStep(pred, ref.getPropertyNameExpr().flow()) and
        result = pred.getStringValue()
      )
    }

    /**
     * Gets unique result of `getAnIndirectPropName` if there is one.
     */
    private string getIndirectPropName(DataFlow::PropRef ref) {
      result = unique(string s | s = getAnIndirectPropName(ref))
    }

    /** Gets the `member` edge label for the given property reference. */
    ApiLabel memberFromRef(DataFlow::PropRef pr) {
      exists(string pn | pn = pr.getPropertyName() or pn = getIndirectPropName(pr) |
        result = member(pn) and
        // only consider properties with alphanumeric(-ish) names, excluding special properties
        // and properties whose names look like they are meant to be internal
        pn.regexpMatch("(?!prototype$|__)[\\w_$][\\w\\-.$]*")
      )
      or
      not exists(pr.getPropertyName()) and
      not exists(getIndirectPropName(pr)) and
      result = unknownMember()
    }

    ApiLabel memberFromPseudoProperty(string prop) {
      prop = Promises::valueProp() and
      result = promised()
      or
      prop = Promises::errorProp() and
      result = promisedError()
    }

    ApiLabel memberFromPropName(string prop) {
      result = memberFromPseudoProperty(prop)
      or
      not exists(memberFromPseudoProperty(prop)) and
      result = member(prop)
    }

    /** Gets the `instance` edge label. */
    LabelInstance instance() { any() }

    /**
     * Gets the `parameter` edge label for the `i`th parameter.
     *
     * The receiver is considered to be parameter -1.
     */
    LabelParameter parameter(int i) { result.getIndex() = i }

    /** Gets the edge label for the receiver. */
    LabelReceiver receiver() { any() }

    /** Gets the `return` edge label. */
    LabelReturn return() { any() }

    /** Gets the `promised` edge label connecting a promise to its contained value. */
    LabelPromised promised() { any() }

    /** Gets the `promisedError` edge label connecting a promise to its rejected value. */
    LabelPromisedError promisedError() { any() }

    /** Gets the label for an edge leading from a value `D` to any class that has `D` as a decorator. */
    LabelDecoratedClass decoratedClass() { any() }

    /** Gets the label for an edge leading from a value `D` to any method, field, or accessor that has `D` as a decorator. */
    LabelDecoratedMethod decoratedMember() { any() }

    /** Gets the label for an edge leading from a value `D` to any parameter that has `D` as a decorator. */
    LabelDecoratedParameter decoratedParameter() { any() }

    private import LabelImpl

    private module LabelImpl {
      newtype TLabel =
        MkLabelModule(string mod) { imports(_, mod) } or
        MkLabelInstance() or
        MkLabelMember(string prop) {
          exists(any(DataFlow::ClassNode c).getInstanceMethod(prop)) or
          prop = "exports" or
          prop = any(CanonicalName c).getName() or
          prop = any(DataFlow::PropRef p).getPropertyName() or
          exists(any(Module m).getAnExportedValue(prop))
        } or
        MkLabelTypeUse(string moduleName, string typeName) {
          any(DataFlow::SourceNode sn).hasUnderlyingType(moduleName, typeName) and
          isViableExternalPackageName(moduleName)
        } or
        MkLabelUnknownMember() or
        MkLabelParameter(int i) {
          i =
            [0 .. max(int args |
                args = any(InvokeExpr invk).getNumArgument() or
                args = any(Function f).getNumParameter()
              )] or
          i = [0 .. 10]
        } or
        MkLabelReceiver() or
        MkLabelReturn() or
        MkLabelPromised() or
        MkLabelPromisedError() or
        MkLabelDecoratedClass() or
        MkLabelDecoratedMember() or
        MkLabelDecoratedParameter()

      /** A label that gets a promised value. */
      class LabelPromised extends ApiLabel, MkLabelPromised {
        override string toString() { result = "getPromised()" }
      }

      /** A label that gets a rejected promise. */
      class LabelPromisedError extends ApiLabel, MkLabelPromisedError {
        override string toString() { result = "getPromisedError()" }
      }

      /** A label that gets the return value of a function. */
      class LabelReturn extends ApiLabel, MkLabelReturn {
        override string toString() { result = "getReturn()" }
      }

      /** A label for a module. */
      class LabelModule extends ApiLabel, MkLabelModule {
        string mod;

        LabelModule() { this = MkLabelModule(mod) }

        /** Gets the module associated with this label. */
        string getMod() { result = mod }

        // moduleImport is not neccesarilly the predicate to use, but it's close enough for most cases.
        override string toString() { result = "moduleImport(\"" + mod + "\")" }
      }

      /** A label that gets an instance from a `new` call. */
      class LabelInstance extends ApiLabel, MkLabelInstance {
        override string toString() { result = "getInstance()" }
      }

      /** A label for the member named `prop`. */
      class LabelMember extends ApiLabel, MkLabelMember {
        string prop;

        LabelMember() { this = MkLabelMember(prop) }

        /** Gets the property associated with this label. */
        string getProperty() { result = prop }

        override string toString() { result = "getMember(\"" + prop + "\")" }
      }

      /** A label for the use of type from a module. */
      class LabelTypeUse extends ApiLabel, MkLabelTypeUse {
        string moduleName;
        string typeName;

        LabelTypeUse() { this = MkLabelTypeUse(moduleName, typeName) }

        /** Gets the module name. */
        string getModuleName() { result = moduleName }

        /** Gets the type name. */
        string getTypeName() { result = typeName }

        override string toString() {
          result = "typeUse(\"" + moduleName + "\",\"" + typeName + "\")"
        }
      }

      /** A label for a member with an unknown name. */
      class LabelUnknownMember extends ApiLabel, MkLabelUnknownMember {
        LabelUnknownMember() { this = MkLabelUnknownMember() }

        override string toString() { result = "getUnknownMember()" }
      }

      /** A label for parameter `i`. */
      class LabelParameter extends ApiLabel, MkLabelParameter {
        int i;

        LabelParameter() { this = MkLabelParameter(i) }

        override string toString() { result = "getParameter(" + i + ")" }

        /** Gets the index of the parameter for this label. */
        int getIndex() { result = i }
      }

      /** A label for the receiver of call, that is, the value passed as `this`. */
      class LabelReceiver extends ApiLabel, MkLabelReceiver {
        override string toString() { result = "getReceiver()" }
      }

      /** A label for a class decorated by the current value. */
      class LabelDecoratedClass extends ApiLabel, MkLabelDecoratedClass {
        override string toString() { result = "getADecoratedClass()" }
      }

      /** A label for a method, field, or accessor decorated by the current value. */
      class LabelDecoratedMethod extends ApiLabel, MkLabelDecoratedMember {
        override string toString() { result = "decoratedMember()" }
      }

      /** A label for a parameter decorated by the current value. */
      class LabelDecoratedParameter extends ApiLabel, MkLabelDecoratedParameter {
        override string toString() { result = "decoratedParameter()" }
      }

      /**
       * Holds if `name` could be an NPM package name.
       *
       * Concretely, this holds if it does not start with a dot or a slash, as these refer
       * to local files.
       */
      bindingset[name]
      private predicate isViableExternalPackageName(string name) { name.regexpMatch("[^./].*") }

      pragma[noinline]
      private predicate isInExterns(DataFlow::Node nd) { nd.getTopLevel().isExterns() }

      /** Holds if `imp` is an import of module `m`. */
      private predicate imports(DataFlow::Node imp, string m) {
        imp = DataFlow::moduleImport(m) and
        isViableExternalPackageName(m) and
        not isInExterns(imp)
      }
    }
  }
}
