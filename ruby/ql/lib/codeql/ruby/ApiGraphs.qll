/**
 * Provides an implementation of  _API graphs_, which are an abstract representation of the API
 * surface used and/or defined by a code base.
 *
 * The nodes of the API graph represent definitions and uses of API components. The edges are
 * directed and labeled; they specify how the components represented by nodes relate to each other.
 */

private import codeql.ruby.AST
private import codeql.ruby.DataFlow
private import codeql.ruby.typetracking.ApiGraphShared
private import codeql.ruby.typetracking.TypeTracker
private import codeql.ruby.typetracking.TypeTrackerSpecific as TypeTrackerSpecific
private import codeql.ruby.controlflow.CfgNodes
private import codeql.ruby.dataflow.internal.DataFlowPrivate as DataFlowPrivate
private import codeql.ruby.dataflow.internal.DataFlowDispatch as DataFlowDispatch

/**
 * Provides classes and predicates for working with APIs used in a database.
 */
module API {
  /**
   * A node in the API graph, that is, a value that can be tracked interprocedurally.
   *
   * The API graph is a graph for tracking values of certain types in a way that accounts for inheritance
   * and interprocedural data flow.
   *
   * API graphs are typically used to identify "API calls", that is, calls to an external function
   * whose implementation is not necessarily part of the current codebase.
   *
   * ### Basic usage
   *
   * The most basic use of API graphs is typically as follows:
   * 1. Start with `API::getTopLevelMember` for the relevant library.
   * 2. Follow up with a chain of accessors such as `getMethod` describing how to get to the relevant API function.
   * 3. Map the resulting API graph nodes to data-flow nodes, using `asSource`, `asSink`, or `asCall`.
   *
   * For example, a simplified way to get arguments to `Foo.bar` would be
   * ```ql
   * API::getTopLevelMember("Foo").getMethod("bar").getParameter(0).asSink()
   * ```
   *
   * The most commonly used accessors are `getMember`, `getMethod`, `getParameter`, and `getReturn`.
   *
   * ### Data flow direction
   *
   * The members predicates on this class generally takes inheritance and data flow into account.
   *
   * For example, consider the API graph expression
   * ```codeql
   * API::getTopLevelMember("Foo").getInstance().getMethod("bar").asCall()
   * ```
   * The above expression would match the `f.bar` call in the following:
   * ```ruby
   * def doSomething f
   *   f.bar
   * end
   * doSomething Foo.new
   * ```
   *
   * When tracking arguments of a call, the data flow direction is backwards.
   * We will illustrate this principle with the following example:
   * ```codeql
   * API::getTopLevelMember("Foo").getInstance().getMethod("bar").getParameter(0).getAnElement().getParameter(0)
   * ```
   * The above expression would match the lamda parameter `x` in the following:
   * ```ruby
   * def doSomething f callbacks
   *   f.bar(callbacks)
   * end
   * doSomething Foo.new [
   *   ->(x) { puts x }
   * ]
   * ```
   * Here's a breakdown of what happens:
   * - `getTopLevelMember("Foo")` gets the access to `Foo`
   * - `.getInstance()` gets the return value of the `Foo.new` call
   * - `.getMethod("bar")` gets the call to `f.bar`. The value `Foo.new` value was implicitly
   *   tracked forwards to the receiver `f`.
   * - `.getParameter(0)` gets the first argument to this call, named `callbacks`.
   * - `.getAnElement()` gets the lambda expression. The `callbacks` argument was implicitly
   *   tracked backwards to the array literal, and the elements of that array literal were then retrieved.
   * - `.getParameter(0)` gets the parameter named `x` in the lambda expression.
   *
   * ### Inheritance
   *
   * When a class or module object is tracked, inheritance is taken into account.
   *
   * For example, consider the API graph expression
   * ```codeql
   * API::getTopLevelMember("Foo").getMethod("bar").asCall()
   * ```
   * The above expression would match the `self.bar` call below, due to `Subclass` inheriting the method `Foo.bar`.
   * ```ruby
   * class Subclass < Foo
   *   def self.doSomething
   *     self.bar # found by API::getTopLevelMember("Foo").getMethod("bar").asCall()
   *   end
   * end
   * ```
   *
   * ### Strict left-to-right evaluation
   *
   * Most member predicates on this class are intended to be chained, and are always evaluated from left to right, which means
   * the caller should restrict the initial set of values.
   *
   * For example, in the following snippet, we always find the uses of `Foo` before finding calls to `bar`:
   * ```ql
   * API::getTopLevelMember("Foo").getMethod("bar")
   * ```
   * In particular, the implementation will never look for calls to `bar` and work backward from there.
   *
   * Beware of the footgun that is to use API graphs with an unrestricted receiver:
   * ```ql
   * API::Node barCall(API::Node base) {
   *   result = base.getMethod("bar") // Do not do this!
   * }
   * ```
   * The above predicate does not restrict the receiver, and will thus perform an interprocedural data flow
   * search starting at every node in the graph, which is very expensive.
   */
  class Node extends Impl::TApiNode {
    /**
     * Gets a data-flow node where this value may flow interprocedurally.
     *
     * This is similar to `asSource()` but additionally includes nodes that are transitively reachable by data flow.
     * See `asSource()` for examples.
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::Node getAValueReachableFromSource() {
      result = getAValueReachableFromSourceInline(this)
    }

    /**
     * Gets a data-flow node where this value enters the current codebase.
     *
     * For example:
     * ```ruby
     * # API::getTopLevelMember("Foo").asSource()
     * Foo
     *
     * # API::getTopLevelMember("Foo").getMethod("bar").getReturn().asSource()
     * Foo.bar
     *
     * # 'x' is found by:
     * # API::getTopLevelMember("Foo").getMethod("bar").getBlock().getParameter(0).asSource()
     * Foo.bar do |x|
     * end
     * ```
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::LocalSourceNode asSource() { result = asSourceInline(this) }

    /**
     * Gets a data-flow node where this value leaves the current codebase and flows into an
     * external library (or in general, any external codebase).
     *
     * Concretely, this corresponds to an argument passed to a call to external code.
     *
     * For example:
     * ```ruby
     * # 'x' is found by:
     * # API::getTopLevelMember("Foo").getMethod("bar").getParameter(0).asSink()
     * Foo.bar(x)
     *
     * Foo.bar(-> {
     *   # 'x' is found by:
     *   # API::getTopLevelMember("Foo").getMethod("bar").getParameter(0).getReturn().asSink()
     *   x
     * })
     * ```
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::Node asSink() { result = asSinkInline(this) }

    /**
     * Get a data-flow node that transitively flows to an external library (or in general, any external codebase).
     *
     * This is similar to `asSink()` but additionally includes nodes that transitively reach a sink by data flow.
     * See `asSink()` for examples.
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::Node getAValueReachingSink() { result = getAValueReachingSinkInline(this) }

    /**
     * Gets a module referred to by this API node.
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::ModuleNode asModule() { this = Impl::MkModuleObjectDown(result) }

    /**
     * Gets the call referred to by this API node.
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::CallNode asCall() { this = Impl::MkMethodAccessNode(result) }

    /**
     * DEPRECATED. Use `asCall()` instead.
     */
    pragma[inline]
    deprecated DataFlow::CallNode getCallNode() { this = Impl::MkMethodAccessNode(result) }

    /**
     * Gets a module that descends from the value referenced by this API node.
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::ModuleNode getADescendentModule() { result = this.getEpsilonSuccessor().asModule() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachableFromSource()`. */
    deprecated DataFlow::Node getAUse() { result = this.getAValueReachableFromSource() }

    /** DEPRECATED. This predicate has been renamed to `asSource()`. */
    deprecated DataFlow::LocalSourceNode getAnImmediateUse() { result = this.asSource() }

    /** DEPRECATED. This predicate has been renamed to `asSink()`. */
    deprecated DataFlow::Node getARhs() { result = this.asSink() }

    /** DEPRECATED. This predicate has been renamed to `getAValueReachingSink()`. */
    deprecated DataFlow::Node getAValueReachingRhs() { result = this.getAValueReachingSink() }

    /**
     * Gets a call to a method on the receiver represented by this API component.
     */
    pragma[inline]
    DataFlow::CallNode getAMethodCall(string method) {
      // This predicate is currently not 'inline_late' because 'method' can be an input or output
      result = this.getMethod(method).asCall()
    }

    /**
     * Gets an access to the constant `m` with this value as the base of the access.
     *
     * For example, the constant `A::B` would be found by `API::getATopLevelMember("A").getMember("B")`
     */
    pragma[inline]
    Node getMember(string m) {
      // This predicate is currently not 'inline_late' because 'm' can be an input or output
      Impl::memberEdge(this.getEpsilonSuccessor(), m, result)
    }

    /**
     * Gets an access to a constant with this valeu as the base of the access.
     */
    bindingset[this]
    pragma[inline_late]
    Node getAMember() { Impl::anyMemberEdge(this.getEpsilonSuccessor(), result) }

    /**
     * Gets an instance of the module or class represented by this API node.
     *
     * This includes the following:
     * - Calls to `new` on this module or a subclass thereof
     * - References to `self` in instance methods in any ancestor of any subclass
     */
    bindingset[this]
    pragma[inline_late]
    Node getInstance() { Impl::instanceEdge(this.getEpsilonSuccessor(), result) }

    /**
     * Gets a call to `method` with this value as the receiver, or the definition of `method` on
     * an object that can reach this sink.
     *
     * If the receiver represents a module object, this includes calls on subclasses of that module.
     */
    pragma[inline]
    Node getMethod(string method) {
      // This predicate is currently not 'inline_late' because 'method' can be an input or output
      Impl::methodEdge(this.getEpsilonSuccessor(), method, result)
    }

    /**
     * Gets the result of this call, or the return value of this callable.
     */
    bindingset[this]
    pragma[inline_late]
    Node getReturn() { Impl::returnEdge(this.getEpsilonSuccessor(), result) }

    /**
     * Gets the result of a call to `method` with this value as the receiver, or the return value of `method` defined on
     * an object that can reach this sink.
     *
     * This is a shorthand for `getMethod(method).getReturn()`.
     */
    pragma[inline]
    Node getReturn(string method) {
      // This predicate is currently not 'inline_late' because 'method' can be an input or output
      result = this.getMethod(method).getReturn()
    }

    /** Gets the `n`th positional argument to this call, or `n`th positional parameter of this callable. */
    pragma[inline]
    Node getParameter(int n) {
      // This predicate is currently not 'inline_late' because 'n' can be an input or output
      Impl::positionalParameterOrArgumentEdge(this.getEpsilonSuccessor(), n, result)
    }

    /** Gets the given keyword argument to this call, or keyword parameter of this callable. */
    pragma[inline]
    Node getKeywordParameter(string name) {
      // This predicate is currently not 'inline_late' because 'name' can be an input or output
      Impl::keywordParameterOrArgumentEdge(this.getEpsilonSuccessor(), name, result)
    }

    /** Gets the block argument to this call, or the block parameter of this callable. */
    bindingset[this]
    pragma[inline_late]
    Node getBlock() { Impl::blockParameterOrArgumentEdge(this.getEpsilonSuccessor(), result) }

    /**
     * Gets the argument passed in argument position `pos` at this call.
     */
    pragma[inline]
    Node getArgumentAtPosition(DataFlowDispatch::ArgumentPosition pos) {
      // This predicate is currently not 'inline_late' because 'pos' can be an input or output
      Impl::argumentEdge(pragma[only_bind_out](this), pos, result) // note: no need for epsilon step since 'this' must be a call
    }

    /**
     * Gets the parameter at position `pos` of this callable.
     */
    pragma[inline]
    Node getParameterAtPosition(DataFlowDispatch::ParameterPosition pos) {
      // This predicate is currently not 'inline_late' because 'pos' can be an input or output
      Impl::parameterEdge(this.getEpsilonSuccessor(), pos, result)
    }

    /**
     * Gets a `new` call with this value as the receiver.
     */
    bindingset[this]
    pragma[inline_late]
    DataFlow::ExprNode getAnInstantiation() { result = this.getReturn("new").asSource() }

    /**
     * Gets a node representing a (direct or indirect) subclass of the class represented by this node.
     * ```rb
     * class A; end
     * class B < A; end
     * class C < B; end
     * ```
     * In the example above, `getMember("A").getASubclass()` will return uses of `A`, `B` and `C`.
     */
    pragma[inline]
    deprecated Node getASubclass() { result = this }

    /**
     * Gets a node representing a direct subclass of the class represented by this node.
     * ```rb
     * class A; end
     * class B < A; end
     * class C < B; end
     * ```
     * In the example above, `getMember("A").getAnImmediateSubclass()` will return uses of `B` only.
     */
    pragma[inline]
    deprecated Node getAnImmediateSubclass() {
      result = this.asModule().getAnImmediateDescendent().trackModule()
    }

    /**
     * Gets a representative for the `content` of this value.
     *
     * When possible, it is preferrable to use one of the specialized variants of this predicate, such as `getAnElement`.
     *
     * Concretely, this gets sources where `content` is read from this value, and as well as sinks where
     * `content` is stored onto this value or onto an object that can reach this sink.
     */
    pragma[inline]
    Node getContent(DataFlow::Content content) {
      // This predicate is currently not 'inline_late' because 'content' can be an input or output
      Impl::contentEdge(this.getEpsilonSuccessor(), content, result)
    }

    /**
     * Gets a representative for the `contents` of this value.
     *
     * See `getContent()` for more details.
     */
    bindingset[this, contents]
    pragma[inline_late]
    Node getContents(DataFlow::ContentSet contents) {
      // We always use getAStoreContent when generating content edges, and we always use getAReadContent when querying the graph.
      result = this.getContent(contents.getAReadContent())
    }

    /**
     * Gets a representative for the instance field of the given `name`, which must include the `@` character.
     */
    pragma[inline]
    Node getField(string name) {
      // This predicate is currently not 'inline_late' because 'name' can be an input or output
      Impl::fieldEdge(this.getEpsilonSuccessor(), name, result)
    }

    /**
     * Gets a representative for an arbitrary element of this collection.
     */
    bindingset[this]
    pragma[inline_late]
    Node getAnElement() { Impl::elementEdge(this.getEpsilonSuccessor(), result) }

    /**
     * DEPRECATED. API graph nodes are no longer associated with specific paths.
     *
     * Gets a string representation of the lexicographically least among all shortest access paths
     * from the root to this node.
     */
    deprecated string getPath() { none() }

    /**
     * DEPRECATED. Use label-specific predicates in this class, such as `getMember`, instead of using `getASuccessor`.
     *
     * Gets a node such that there is an edge in the API graph between this node and the other
     * one, and that edge is labeled with `lbl`.
     */
    pragma[inline]
    deprecated Node getASuccessor(Label::ApiLabel lbl) {
      labelledEdge(this.getEpsilonSuccessor(), lbl, result)
    }

    /**
     * DEPRECATED. API graphs no longer support backward traversal of edges. If possible use `.backtrack()` to get
     * a node intended for backtracking.
     *
     * Gets a node such that there is an edge in the API graph between that other node and
     * this one, and that edge is labeled with `lbl`
     */
    deprecated Node getAPredecessor(Label::ApiLabel lbl) { this = result.getASuccessor(lbl) }

    /**
     * DEPRECATED. API graphs no longer support backward traversal of edges. If possible use `.backtrack()` to get
     * a node intended for backtracking.
     *
     * Gets a node such that there is an edge in the API graph between this node and the other
     * one.
     */
    deprecated Node getAPredecessor() { result = this.getAPredecessor(_) }

    /**
     * Gets a node such that there is an edge in the API graph between that other node and
     * this one.
     */
    pragma[inline]
    deprecated Node getASuccessor() { result = this.getASuccessor(_) }

    /**
     * Gets the data-flow node that gives rise to this node, if any.
     */
    DataFlow::Node getInducingNode() {
      this = Impl::MkMethodAccessNode(result) or
      this = Impl::MkBackwardNode(result, _) or
      this = Impl::MkForwardNode(result, _) or
      this = Impl::MkSinkNode(result)
    }

    /** Gets the location of this node. */
    Location getLocation() {
      result = this.getInducingNode().getLocation()
      or
      exists(DataFlow::ModuleNode mod |
        this = Impl::MkModuleObjectDown(mod)
        or
        this = Impl::MkModuleInstanceUp(mod)
      |
        result = mod.getLocation()
      )
      or
      this instanceof RootNode and
      result instanceof EmptyLocation
    }

    /**
     * Gets a textual representation of this element.
     */
    string toString() { none() }

    /** DEPRECATED. API graphs are no longer associated with a depth. */
    deprecated int getDepth() { none() }

    pragma[inline]
    private Node getEpsilonSuccessor() { result = getEpsilonSuccessorInline(this) }
  }

  /** DEPRECATED. Use `API::root()` to access the root node. */
  deprecated class Root = RootNode;

  /** DEPRECATED. A node corresponding to the use of an API component. */
  deprecated class Use = ForwardNode;

  /** DEPRECATED. A node corresponding to a value escaping into an API component. */
  deprecated class Def = BackwardNode; // TODO use sink node instead?

  /** The root node of an API graph. */
  private class RootNode extends Node, Impl::MkRoot {
    override string toString() { result = "Root()" }
  }

  /** A node representing a given type-tracking state when tracking forwards. */
  private class ForwardNode extends Node {
    private DataFlow::LocalSourceNode node;
    private TypeTracker tracker;

    ForwardNode() { this = Impl::MkForwardNode(node, tracker) }

    override string toString() {
      if tracker.start()
      then result = "ForwardNode(" + node + ")"
      else result = "ForwardNode(" + node + ", " + tracker + ")"
    }
  }

  /** A node representing a given type-tracking state when tracking backwards. */
  private class BackwardNode extends Node {
    private DataFlow::LocalSourceNode node;
    private TypeTracker tracker;

    BackwardNode() { this = Impl::MkBackwardNode(node, tracker) }

    override string toString() {
      if tracker.start()
      then result = "BackwardNode(" + node + ")"
      else result = "BackwardNode(" + node + ", " + tracker + ")"
    }
  }

  /** A node representing the module/class object for a given module or class. */
  private class ModuleObjectUpNode extends Node {
    ModuleObjectUpNode() { this instanceof Impl::MkModuleObjectDown }

    /** Gets the module represented by this API node. */
    DataFlow::ModuleNode getModule() { this = Impl::MkModuleObjectDown(result) }

    override string toString() { result = "ModuleObjectDown(" + this.getModule() + ")" }
  }

  /** A node representing a module/class object escaping into external code. */
  private class ModuleObjectDownNode extends Node {
    ModuleObjectDownNode() { this instanceof Impl::MkModuleObjectUp }

    /** Gets the module represented by this API node. */
    DataFlow::ModuleNode getModule() { this = Impl::MkModuleObjectUp(result) }

    override string toString() { result = "ModuleObjectUp(" + this.getModule() + ")" }
  }

  /** A node representing instances of a module/class and its ancestors. */
  private class ModuleInstanceUpNode extends Node {
    ModuleInstanceUpNode() { this instanceof Impl::MkModuleInstanceUp }

    /** Gets the module whose instances are represented by this API node. */
    DataFlow::ModuleNode getModule() { this = Impl::MkModuleInstanceUp(result) }

    override string toString() { result = "ModuleInstanceUp(" + this.getModule() + ")" }
  }

  /** A node representing instances of a module/class and its descendents. */
  private class ModuleInstanceDownNode extends Node {
    ModuleInstanceDownNode() { this instanceof Impl::MkModuleInstanceDown }

    /** Gets the module whose instances are represented by this API node. */
    DataFlow::ModuleNode getModule() { this = Impl::MkModuleInstanceDown(result) }

    override string toString() { result = "ModuleInstanceDown(" + this.getModule() + ")" }
  }

  /** A node corresponding to the method being invoked at a method call. */
  class MethodAccessNode extends Node, Impl::MkMethodAccessNode {
    override string toString() { result = "MethodAccessNode(" + this.asCall() + ")" }
  }

  /**
   * A node corresponding to an argument or right-hand side of a store edge.
   *
   * Such a node may serve as the starting-point of backtracking, and has epsilon edges going
   * the backward nodes corresponding to `getALocalSource`.
   */
  private class SinkNode extends Node, Impl::MkSinkNode {
    override string toString() { result = "SinkNode(" + this.getInducingNode() + ")" }
  }

  /**
   * An API entry point.
   *
   * By default, API graph nodes are only created for nodes that come from an external
   * library or escape into an external library. The points where values are cross the boundary
   * between codebases are called "entry points".
   *
   * Anything in the global scope is considered to be an entry point, but
   * additional entry points may be added by extending this class.
   */
  abstract class EntryPoint extends string {
    // Note: this class can be deprecated in Ruby, but is still referenced by shared code in ApiGraphModels.qll,
    // where it can't be removed since other languages are still dependent on the EntryPoint class.
    bindingset[this]
    EntryPoint() { any() }

    /** DEPRECATED. This predicate has been renamed to `getASource`. */
    deprecated DataFlow::LocalSourceNode getAUse() { none() }

    /** DEPRECATED. This predicate has been renamed to `getASink`. */
    deprecated DataFlow::Node getARhs() { none() }

    /** Gets a data-flow node corresponding to a use-node for this entry point. */
    DataFlow::LocalSourceNode getASource() { none() }

    /** Gets a data-flow node corresponding to a def-node for this entry point. */
    DataFlow::Node getASink() { none() }

    /** Gets a call corresponding to a method access node for this entry point. */
    DataFlow::CallNode getACall() { none() }

    /** Gets an API-node for this entry point. */
    API::Node getANode() { Impl::entryPointEdge(this, result) }
  }

  // Ensure all entry points are imported from ApiGraphs.qll
  private module ImportEntryPoints {
    private import codeql.ruby.frameworks.data.ModelsAsData
  }

  /** Gets the root node. */
  Node root() { result instanceof RootNode }

  /**
   * Gets an access to the top-level constant `name`.
   *
   * To access nested constants, use `getMember()` on the resulting node. For example, for nodes corresponding to the class `Gem::Version`,
   * use `getTopLevelMember("Gem").getMember("Version")`.
   */
  pragma[inline]
  Node getTopLevelMember(string name) { Impl::topLevelMember(name, result) }

  /**
   * Gets an unqualified call at the top-level with the given method name.
   */
  pragma[inline]
  MethodAccessNode getTopLevelCall(string name) { Impl::toplevelCall(name, result) }

  pragma[nomagic]
  private predicate isReachable(DataFlow::LocalSourceNode node, TypeTracker t) {
    t.start() and exists(node)
    or
    exists(DataFlow::LocalSourceNode prev, TypeTracker t2 |
      isReachable(prev, t2) and
      node = prev.track(t2, t) and
      notSelfParameter(node)
    )
  }

  bindingset[node]
  pragma[inline_late]
  private predicate notSelfParameter(DataFlow::Node node) {
    not node instanceof DataFlow::SelfParameterNode
  }

  bindingset[node]
  pragma[inline_late]
  private DataFlow::LocalSourceNode getALocalSource(DataFlow::Node node) {
    result = node.getALocalSource()
  }

  private module SharedArg implements ApiGraphSharedSig {
    class ApiNode = Node;

    ApiNode getForwardNode(DataFlow::LocalSourceNode node, TypeTracker t) {
      result = Impl::MkForwardNode(node, t)
    }

    ApiNode getBackwardNode(DataFlow::LocalSourceNode node, TypeTracker t) {
      result = Impl::MkBackwardNode(node, t)
    }

    ApiNode getSinkNode(DataFlow::Node node) { result = Impl::MkSinkNode(node) }

    pragma[nomagic]
    predicate specificEpsilonEdge(ApiNode pred, ApiNode succ) {
      exists(DataFlow::ModuleNode mod |
        moduleReferenceEdge(mod, pred, succ)
        or
        moduleInheritanceEdge(mod, pred, succ)
        or
        implicitCallEdge(pred, succ)
        or
        pred = getForwardEndNode(getSuperClassNode(mod)) and
        succ = Impl::MkModuleObjectDown(mod)
      )
      or
      exists(DataFlow::HashLiteralNode splat | hashSplatEdge(splat, pred, succ))
    }

    pragma[nomagic]
    private DataFlow::Node getHashSplatArgument(DataFlow::HashLiteralNode literal) {
      result = DataFlowPrivate::TSynthHashSplatArgumentNode(literal.asExpr())
    }

    /**
     * Holds if the epsilon edge `pred -> succ` should be generated, to handle inheritance relations of `mod`.
     */
    pragma[inline]
    private predicate moduleInheritanceEdge(DataFlow::ModuleNode mod, ApiNode pred, ApiNode succ) {
      pred = Impl::MkModuleObjectDown(mod) and
      succ = Impl::MkModuleObjectDown(mod.getAnImmediateDescendent())
      or
      pred = Impl::MkModuleInstanceDown(mod) and
      succ = Impl::MkModuleInstanceDown(mod.getAnImmediateDescendent())
      or
      exists(DataFlow::ModuleNode ancestor |
        ancestor = mod.getAnImmediateAncestor() and
        // Restrict flow back to Object to avoid spurious flow for methods that happen
        // to exist on Object, such as top-level methods.
        not ancestor.getQualifiedName() = "Object"
      |
        pred = Impl::MkModuleInstanceUp(mod) and
        succ = Impl::MkModuleInstanceUp(ancestor)
        or
        pred = Impl::MkModuleObjectUp(mod) and
        succ = Impl::MkModuleObjectUp(ancestor)
      )
      or
      // Due to multiple inheritance, allow upwards traversal after downward traversal,
      // so we can detect calls sideways in the hierarchy.
      // Note that a similar case does not exist for ModuleObject since singleton methods are only inherited
      // from the superclass, and there can only be one superclass.
      pred = Impl::MkModuleInstanceDown(mod) and
      succ = Impl::MkModuleInstanceUp(mod)
    }

    /**
     * Holds if the epsilon `pred -> succ` be generated, to associate `mod` with its references in the codebase.
     */
    bindingset[mod]
    pragma[inline_late]
    private predicate moduleReferenceEdge(DataFlow::ModuleNode mod, ApiNode pred, ApiNode succ) {
      pred = Impl::MkModuleObjectDown(mod) and
      succ = getForwardStartNode(getAModuleReference(mod))
      or
      pred = getBackwardEndNode(getAModuleReference(mod)) and
      (
        succ = Impl::MkModuleObjectUp(mod)
        or
        succ = Impl::MkModuleObjectDown(mod)
      )
      or
      pred = Impl::MkModuleInstanceUp(mod) and
      succ = getAModuleInstanceUseNode(mod)
      or
      pred = getAModuleInstanceDefNode(mod) and
      succ = Impl::MkModuleInstanceUp(mod)
      or
      pred = getAModuleDescendentInstanceDefNode(mod) and
      succ = Impl::MkModuleInstanceDown(mod)
    }

    /**
     * Holds if the epsilon step `pred -> succ` should be generated to account for the fact that `getMethod("call")`
     * may be omitted when dealing with blocks, lambda, or procs.
     *
     * For example, a block may be invoked by a `yield`, or can be converted to a proc or lambda and then invoked via `.call`.
     * To simplify this, lambad/proc conversion is seen as a no-op and the `.call` is omitted.
     */
    pragma[nomagic]
    private predicate implicitCallEdge(ApiNode pred, ApiNode succ) {
      // Step from &block parameter to yield call without needing `getMethod("call")`.
      exists(DataFlow::MethodNode method |
        pred = getForwardStartNode(method.getBlockParameter()) and
        succ = Impl::MkMethodAccessNode(method.getABlockCall())
      )
      or
      // Step from x -> x.call (the call itself, not its return value), without needing `getMethod("call")`.
      exists(DataFlow::CallNode call |
        call.getMethodName() = "call" and
        pred = getForwardEndNode(getALocalSource(call.getReceiver())) and
        succ = Impl::MkMethodAccessNode(call)
      )
      or
      exists(DataFlow::ModuleNode mod |
        // Step from module/class to its own `call` method withouht needing `getMethod("call")`.
        (pred = Impl::MkModuleObjectDown(mod) or pred = Impl::MkModuleObjectUp(mod)) and
        succ = getBackwardEndNode(mod.getOwnSingletonMethod("call"))
        or
        pred = Impl::MkModuleInstanceUp(mod) and
        succ = getBackwardEndNode(mod.getOwnInstanceMethod("call"))
      )
    }

    /**
     * Holds if the epsilon edge `pred -> succ` should be generated to account for the members of a hash literal.
     *
     * This currently exists because hash literals are desugared to `Hash.[]` calls, whose summary relies on `WithContent`.
     * However, `contentEdge` does not currently generate edges for `WithContent` steps.
     */
    bindingset[literal]
    pragma[inline_late]
    private predicate hashSplatEdge(DataFlow::HashLiteralNode literal, ApiNode pred, ApiNode succ) {
      exists(TypeTracker t |
        pred = Impl::MkForwardNode(getALocalSource(getHashSplatArgument(literal)), t) and
        succ = Impl::MkForwardNode(pragma[only_bind_out](literal), pragma[only_bind_out](t))
        or
        succ = Impl::MkBackwardNode(getALocalSource(getHashSplatArgument(literal)), t) and
        pred = Impl::MkBackwardNode(pragma[only_bind_out](literal), pragma[only_bind_out](t))
      )
    }

    pragma[nomagic]
    private DataFlow::LocalSourceNode getAModuleReference(DataFlow::ModuleNode mod) {
      result = mod.getAnImmediateReference()
      or
      mod.getAnAncestor().getAnOwnInstanceSelf() = getANodeReachingClassCall(result)
    }

    /**
     * Gets an API node that may refer to an instance of `mod`.
     */
    bindingset[mod]
    pragma[inline_late]
    private ApiNode getAModuleInstanceUseNode(DataFlow::ModuleNode mod) {
      result = getForwardStartNode(mod.getAnOwnInstanceSelf())
    }

    /**
     * Gets a node that can be backtracked to an instance of `mod`.
     */
    bindingset[mod]
    pragma[inline_late]
    private ApiNode getAModuleInstanceDefNode(DataFlow::ModuleNode mod) {
      result = getBackwardEndNode(mod.getAnImmediateReference().getAMethodCall("new"))
    }

    bindingset[mod]
    pragma[inline_late]
    private ApiNode getAModuleDescendentInstanceDefNode(DataFlow::ModuleNode mod) {
      result = getBackwardEndNode(mod.getAnOwnInstanceSelf())
    }

    /**
     * Holds if `superclass` is the superclass of `mod`.
     */
    pragma[nomagic]
    private DataFlow::LocalSourceNode getSuperClassNode(DataFlow::ModuleNode mod) {
      result.getALocalUse().asExpr().getExpr() =
        mod.getADeclaration().(ClassDeclaration).getSuperclassExpr()
    }

    /** Gets a node that can reach the receiver of the given `.class` call. */
    private DataFlow::LocalSourceNode getANodeReachingClassCall(
      DataFlow::CallNode call, TypeBackTracker t
    ) {
      t.start() and
      call.getMethodName() = "class" and
      result = getALocalSource(call.getReceiver())
      or
      exists(DataFlow::LocalSourceNode prev, TypeBackTracker t2 |
        prev = getANodeReachingClassCall(call, t2) and
        result = prev.backtrack(t2, t) and
        notSelfParameter(prev)
      )
    }

    /** Gets a node that can reach the receiver of the given `.class` call. */
    private DataFlow::LocalSourceNode getANodeReachingClassCall(DataFlow::CallNode call) {
      result = getANodeReachingClassCall(call, TypeBackTracker::end())
    }
  }

  /** INTERNAL USE ONLY. */
  module Internal {
    private module Shared = ApiGraphShared<SharedArg>;

    import Shared

    /** Gets the API node corresponding to the module/class object for `mod`. */
    bindingset[mod]
    pragma[inline_late]
    Node getModuleNode(DataFlow::ModuleNode mod) { result = Impl::MkModuleObjectDown(mod) }

    /** Gets the API node corresponding to instances of `mod`. */
    bindingset[mod]
    pragma[inline_late]
    Node getModuleInstance(DataFlow::ModuleNode mod) { result = getModuleNode(mod).getInstance() }
  }

  private import Internal

  cached
  private module Impl {
    cached
    newtype TApiNode =
      /** The root of the API graph. */
      MkRoot() or
      /** The method accessed at `call`, synthetically treated as a separate object. */
      MkMethodAccessNode(DataFlow::CallNode call) or
      /** The module object `mod` with epsilon edges to its ancestors. */
      MkModuleObjectUp(DataFlow::ModuleNode mod) or
      /** The module object `mod` with epsilon edges to its descendents. */
      MkModuleObjectDown(DataFlow::ModuleNode mod) or
      /** Instances of `mod` with epsilon edges to its ancestors. */
      MkModuleInstanceUp(DataFlow::ModuleNode mod) or
      /** Instances of `mod` with epsilon edges to its descendents, and to its upward node. */
      MkModuleInstanceDown(DataFlow::ModuleNode mod) or
      /** Intermediate node for tracking use-nodes. */
      MkForwardNode(DataFlow::LocalSourceNode node, TypeTracker t) { isReachable(node, t) } or
      /** Intermediate node for tracking def-nodes. */
      MkBackwardNode(DataFlow::LocalSourceNode node, TypeTracker t) { isReachable(node, t) } or
      MkSinkNode(DataFlow::Node node) { needsSinkNode(node) }

    private predicate needsSinkNode(DataFlow::Node node) {
      node instanceof DataFlowPrivate::ArgumentNode
      or
      TypeTrackerSpecific::basicStoreStep(node, _, _)
      or
      node = any(DataFlow::CallableNode callable).getAReturnNode()
      or
      node = any(EntryPoint e).getASink()
    }

    bindingset[e]
    pragma[inline_late]
    private DataFlow::Node getNodeFromExpr(Expr e) { result.asExpr().getExpr() = e }

    private string resolveTopLevel(ConstantReadAccess read) {
      result = read.getModule().getQualifiedName() and
      not result.matches("%::%")
    }

    /**
     * Holds `pred` should have a member edge to `mod`.
     */
    pragma[nomagic]
    private predicate moduleScope(DataFlow::ModuleNode mod, Node pred, string name) {
      exists(Namespace namespace |
        name = namespace.getName() and
        namespace = mod.getADeclaration()
      |
        exists(DataFlow::Node scopeNode |
          scopeNode.asExpr().getExpr() = namespace.getScopeExpr() and
          pred = getForwardEndNode(getALocalSource(scopeNode))
        )
        or
        not exists(namespace.getScopeExpr()) and
        if namespace.hasGlobalScope() or namespace.getEnclosingModule() instanceof Toplevel
        then pred = MkRoot()
        else pred = MkModuleObjectDown(namespace.getEnclosingModule().getModule())
      )
    }

    cached
    predicate memberEdge(Node pred, string name, Node succ) {
      exists(ConstantReadAccess read | succ = getForwardStartNode(getNodeFromExpr(read)) |
        name = resolveTopLevel(read) and
        pred = MkRoot()
        or
        not exists(resolveTopLevel(read)) and
        not exists(read.getScopeExpr()) and
        name = read.getName() and
        pred = MkRoot()
        or
        pred = getForwardEndNode(getALocalSource(getNodeFromExpr(read.getScopeExpr()))) and
        name = read.getName()
      )
      or
      exists(DataFlow::ModuleNode mod |
        moduleScope(mod, pred, name) and
        (succ = MkModuleObjectDown(mod) or succ = MkModuleObjectUp(mod))
      )
    }

    cached
    predicate topLevelMember(string name, Node node) { memberEdge(root(), name, node) }

    cached
    predicate toplevelCall(string name, Node node) {
      exists(DataFlow::CallNode call |
        call.asExpr().getExpr().getCfgScope() instanceof Toplevel and
        call.getMethodName() = name and
        node = MkMethodAccessNode(call)
      )
    }

    cached
    predicate anyMemberEdge(Node pred, Node succ) { memberEdge(pred, _, succ) }

    cached
    predicate methodEdge(Node pred, string name, Node succ) {
      exists(DataFlow::ModuleNode mod, DataFlow::CallNode call |
        // Treat super calls as if they were calls to the module object/instance.
        succ = MkMethodAccessNode(call) and
        name = call.getMethodName()
      |
        pred = MkModuleObjectDown(mod) and
        call = mod.getAnOwnSingletonMethod().getASuperCall()
        or
        pred = MkModuleInstanceUp(mod) and
        call = mod.getAnOwnInstanceMethod().getASuperCall()
      )
      or
      exists(DataFlow::CallNode call |
        // from receiver to method call node
        pred = getForwardEndNode(getALocalSource(call.getReceiver())) and
        succ = MkMethodAccessNode(call) and
        name = call.getMethodName()
      )
      or
      exists(DataFlow::ModuleNode mod |
        (pred = MkModuleObjectDown(mod) or pred = MkModuleObjectUp(mod)) and
        succ = getBackwardStartNode(mod.getOwnSingletonMethod(name))
        or
        pred = MkModuleInstanceUp(mod) and
        succ = getBackwardStartNode(mod.getOwnInstanceMethod(name))
      )
    }

    cached
    predicate contentEdge(Node pred, DataFlow::Content content, Node succ) {
      exists(
        DataFlow::Node object, DataFlow::Node value, TypeTrackerSpecific::TypeTrackerContent c
      |
        TypeTrackerSpecific::basicLoadStep(object, value, c) and
        content = c.getAStoreContent() and
        not c.isSingleton(any(DataFlow::Content::AttributeNameContent k)) and
        // `x -> x.foo` with content "foo"
        pred = getForwardOrBackwardEndNode(getALocalSource(object)) and
        succ = getForwardStartNode(value)
        or
        // Based on `object.c = value` generate `object -> value` with content `c`
        TypeTrackerSpecific::basicStoreStep(value, object, c) and
        content = c.getAStoreContent() and
        pred = getForwardOrBackwardEndNode(getALocalSource(object)) and
        succ = MkSinkNode(value)
      )
    }

    cached
    predicate fieldEdge(Node pred, string name, Node succ) {
      Impl::contentEdge(pred, DataFlowPrivate::TFieldContent(name), succ)
    }

    cached
    predicate elementEdge(Node pred, Node succ) {
      contentEdge(pred, any(DataFlow::ContentSet set | set.isAnyElement()).getAReadContent(), succ)
    }

    cached
    predicate parameterEdge(Node pred, DataFlowDispatch::ParameterPosition paramPos, Node succ) {
      exists(DataFlowPrivate::ParameterNodeImpl parameter, DataFlow::CallableNode callable |
        parameter.isSourceParameterOf(callable.asExpr().getExpr(), paramPos) and
        pred = getBackwardEndNode(callable) and
        succ = getForwardStartNode(parameter)
      )
    }

    cached
    predicate argumentEdge(Node pred, DataFlowDispatch::ArgumentPosition argPos, Node succ) {
      exists(DataFlow::CallNode call, DataFlowPrivate::ArgumentNode argument |
        argument.sourceArgumentOf(call.asExpr(), argPos) and
        pred = MkMethodAccessNode(call) and
        succ = MkSinkNode(argument)
      )
    }

    cached
    predicate positionalParameterOrArgumentEdge(Node pred, int n, Node succ) {
      parameterEdge(pred, any(DataFlowDispatch::ParameterPosition pos | pos.isPositional(n)), succ)
      or
      argumentEdge(pred, any(DataFlowDispatch::ArgumentPosition pos | pos.isPositional(n)), succ)
    }

    cached
    predicate keywordParameterOrArgumentEdge(Node pred, string name, Node succ) {
      parameterEdge(pred, any(DataFlowDispatch::ParameterPosition pos | pos.isKeyword(name)), succ)
      or
      argumentEdge(pred, any(DataFlowDispatch::ArgumentPosition pos | pos.isKeyword(name)), succ)
    }

    cached
    predicate blockParameterOrArgumentEdge(Node pred, Node succ) {
      parameterEdge(pred, any(DataFlowDispatch::ParameterPosition pos | pos.isBlock()), succ)
      or
      argumentEdge(pred, any(DataFlowDispatch::ArgumentPosition pos | pos.isBlock()), succ)
    }

    pragma[nomagic]
    private predicate newCall(DataFlow::LocalSourceNode receiver, DataFlow::CallNode call) {
      call = receiver.getAMethodCall("new")
    }

    cached
    predicate instanceEdge(Node pred, Node succ) {
      exists(DataFlow::ModuleNode mod |
        pred = MkModuleObjectDown(mod) and
        succ = MkModuleInstanceUp(mod)
      )
      or
      exists(DataFlow::LocalSourceNode receiver, DataFlow::CallNode call |
        newCall(receiver, call) and
        pred = getForwardEndNode(receiver) and
        succ = getForwardStartNode(call)
      )
    }

    cached
    predicate returnEdge(Node pred, Node succ) {
      exists(DataFlow::CallNode call |
        pred = MkMethodAccessNode(call) and
        succ = getForwardStartNode(call)
      )
      or
      exists(DataFlow::CallableNode callable |
        pred = getBackwardEndNode(callable) and
        succ = MkSinkNode(callable.getAReturnNode())
      )
    }

    cached
    predicate entryPointEdge(EntryPoint entry, Node node) {
      node = MkSinkNode(entry.getASink()) or
      node = getForwardStartNode(entry.getASource()) or
      node = MkMethodAccessNode(entry.getACall())
    }
  }

  /**
   * Holds if there is an edge from `pred` to `succ` in the API graph that is labeled with `lbl`.
   */
  pragma[nomagic]
  deprecated private predicate labelledEdge(Node pred, Label::ApiLabel lbl, Node succ) {
    exists(string name |
      Impl::memberEdge(pred, name, succ) and
      lbl = Label::member(name)
    )
    or
    exists(string name |
      Impl::methodEdge(pred, name, succ) and
      lbl = Label::method(name)
    )
    or
    exists(DataFlow::Content content |
      Impl::contentEdge(pred, content, succ) and
      lbl = Label::content(content)
    )
    or
    exists(DataFlowDispatch::ParameterPosition pos |
      Impl::parameterEdge(pred, pos, succ) and
      lbl = Label::getLabelFromParameterPosition(pos)
    )
    or
    exists(DataFlowDispatch::ArgumentPosition pos |
      Impl::argumentEdge(pred, pos, succ) and
      lbl = Label::getLabelFromArgumentPosition(pos)
    )
    or
    Impl::instanceEdge(pred, succ) and
    lbl = Label::instance()
    or
    Impl::returnEdge(pred, succ) and
    lbl = Label::return()
    or
    exists(EntryPoint entry |
      Impl::entryPointEdge(entry, succ) and
      pred = root() and
      lbl = Label::entryPoint(entry)
    )
  }

  /**
   * DEPRECATED. Treating the API graph as an explicit labelled graph is deprecated - instead use the methods on `API:Node` directly.
   *
   * Provides classes modeling the various edges (labels) in the API graph.
   */
  deprecated module Label {
    /** All the possible labels in the API graph. */
    private newtype TLabel =
      MkLabelMember(string member) { member = any(ConstantReadAccess a).getName() } or
      MkLabelMethod(string m) { m = any(DataFlow::CallNode c).getMethodName() } or
      MkLabelReturn() or
      MkLabelInstance() or
      MkLabelKeywordParameter(string name) {
        any(DataFlowDispatch::ArgumentPosition arg).isKeyword(name)
        or
        any(DataFlowDispatch::ParameterPosition arg).isKeyword(name)
      } or
      MkLabelParameter(int n) {
        any(DataFlowDispatch::ArgumentPosition c).isPositional(n)
        or
        any(DataFlowDispatch::ParameterPosition c).isPositional(n)
      } or
      MkLabelBlockParameter() or
      MkLabelEntryPoint(EntryPoint name) or
      MkLabelContent(DataFlow::Content content)

    /** A label in the API-graph */
    class ApiLabel extends TLabel {
      /** Gets a string representation of this label. */
      string toString() { result = "???" }
    }

    private import LabelImpl

    private module LabelImpl {
      private import Impl

      /** A label for a member, for example a constant. */
      class LabelMember extends ApiLabel, MkLabelMember {
        private string member;

        LabelMember() { this = MkLabelMember(member) }

        /** Gets the member name associated with this label. */
        string getMember() { result = member }

        override string toString() { result = "getMember(\"" + member + "\")" }
      }

      /** A label for a method. */
      class LabelMethod extends ApiLabel, MkLabelMethod {
        private string method;

        LabelMethod() { this = MkLabelMethod(method) }

        /** Gets the method name associated with this label. */
        string getMethod() { result = method }

        override string toString() { result = "getMethod(\"" + method + "\")" }
      }

      /** A label for the return value of a method. */
      class LabelReturn extends ApiLabel, MkLabelReturn {
        override string toString() { result = "getReturn()" }
      }

      /** A label for getting instances of a module/class. */
      class LabelInstance extends ApiLabel, MkLabelInstance {
        override string toString() { result = "getInstance()" }
      }

      /** A label for a keyword parameter. */
      class LabelKeywordParameter extends ApiLabel, MkLabelKeywordParameter {
        private string name;

        LabelKeywordParameter() { this = MkLabelKeywordParameter(name) }

        /** Gets the name of the keyword parameter associated with this label. */
        string getName() { result = name }

        override string toString() { result = "getKeywordParameter(\"" + name + "\")" }
      }

      /** A label for a parameter. */
      class LabelParameter extends ApiLabel, MkLabelParameter {
        private int n;

        LabelParameter() { this = MkLabelParameter(n) }

        /** Gets the parameter number associated with this label. */
        int getIndex() { result = n }

        override string toString() { result = "getParameter(" + n + ")" }
      }

      /** A label for a block parameter. */
      class LabelBlockParameter extends ApiLabel, MkLabelBlockParameter {
        override string toString() { result = "getBlock()" }
      }

      /** A label from the root node to a custom entry point. */
      class LabelEntryPoint extends ApiLabel, MkLabelEntryPoint {
        private API::EntryPoint name;

        LabelEntryPoint() { this = MkLabelEntryPoint(name) }

        override string toString() { result = "entryPoint(\"" + name + "\")" }

        /** Gets the name of the entry point. */
        API::EntryPoint getName() { result = name }
      }

      /** A label representing contents of an object. */
      class LabelContent extends ApiLabel, MkLabelContent {
        private DataFlow::Content content;

        LabelContent() { this = MkLabelContent(content) }

        override string toString() {
          result = "getContent(" + content.toString().replaceAll(" ", "_") + ")"
        }

        /** Gets the content represented by this label. */
        DataFlow::Content getContent() { result = content }
      }
    }

    /** Gets the `member` edge label for member `m`. */
    LabelMember member(string m) { result.getMember() = m }

    /** Gets the `method` edge label. */
    LabelMethod method(string m) { result.getMethod() = m }

    /** Gets the `return` edge label. */
    LabelReturn return() { any() }

    /** Gets the `instance` edge label. */
    LabelInstance instance() { any() }

    /** Gets the label representing the given keyword argument/parameter. */
    LabelKeywordParameter keywordParameter(string name) { result.getName() = name }

    /** Gets the label representing the `n`th positional argument/parameter. */
    LabelParameter parameter(int n) { result.getIndex() = n }

    /** Gets the label representing the block argument/parameter. */
    LabelBlockParameter blockParameter() { any() }

    /** Gets the label for the edge from the root node to a custom entry point of the given name. */
    LabelEntryPoint entryPoint(API::EntryPoint name) { result.getName() = name }

    /** Gets a label representing the given content. */
    LabelContent content(DataFlow::Content content) { result.getContent() = content }

    /** Gets the API graph label corresponding to the given argument position. */
    Label::ApiLabel getLabelFromArgumentPosition(DataFlowDispatch::ArgumentPosition pos) {
      exists(int n |
        pos.isPositional(n) and
        result = Label::parameter(n)
      )
      or
      exists(string name |
        pos.isKeyword(name) and
        result = Label::keywordParameter(name)
      )
      or
      pos.isBlock() and
      result = Label::blockParameter()
      or
      pos.isAny() and
      (
        result = Label::parameter(_)
        or
        result = Label::keywordParameter(_)
        or
        result = Label::blockParameter()
        // NOTE: `self` should NOT be included, as described in the QLDoc for `isAny()`
      )
      or
      pos.isAnyNamed() and
      result = Label::keywordParameter(_)
      //
      // Note: there is currently no API graph label for `self`.
      // It was omitted since in practice it means going back to where you came from.
      // For example, `base.getMethod("foo").getSelf()` would just be `base`.
      // However, it's possible we'll need it later, for identifying `self` parameters or post-update nodes.
    }

    /** Gets the API graph label corresponding to the given parameter position. */
    Label::ApiLabel getLabelFromParameterPosition(DataFlowDispatch::ParameterPosition pos) {
      exists(int n |
        pos.isPositional(n) and
        result = Label::parameter(n)
      )
      or
      exists(string name |
        pos.isKeyword(name) and
        result = Label::keywordParameter(name)
      )
      or
      pos.isBlock() and
      result = Label::blockParameter()
      or
      pos.isAny() and
      (
        result = Label::parameter(_)
        or
        result = Label::keywordParameter(_)
        or
        result = Label::blockParameter()
        // NOTE: `self` should NOT be included, as described in the QLDoc for `isAny()`
      )
      or
      pos.isAnyNamed() and
      result = Label::keywordParameter(_)
      //
      // Note: there is currently no API graph label for `self`.
      // It was omitted since in practice it means going back to where you came from.
      // For example, `base.getMethod("foo").getSelf()` would just be `base`.
      // However, it's possible we'll need it later, for identifying `self` parameters or post-update nodes.
    }
  }
}
