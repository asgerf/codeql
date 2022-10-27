private import codeql.ruby.AST
private import DataFlowDispatch
private import DataFlowPrivate
private import codeql.ruby.CFG
private import codeql.ruby.typetracking.TypeTracker
private import codeql.ruby.dataflow.SSA
private import FlowSummaryImpl as FlowSummaryImpl
private import SsaImpl as SsaImpl

/**
 * An element, viewed as a node in a data flow graph. Either an expression
 * (`ExprNode`) or a parameter (`ParameterNode`).
 */
class Node extends TNode {
  /** Gets the expression corresponding to this node, if any. */
  CfgNodes::ExprCfgNode asExpr() { result = this.(ExprNode).getExprNode() }

  /** Gets the parameter corresponding to this node, if any. */
  Parameter asParameter() { result = this.(ParameterNode).getParameter() }

  /** Gets a textual representation of this node. */
  cached
  final string toString() { result = this.(NodeImpl).toStringImpl() }

  /** Gets the location of this node. */
  cached
  final Location getLocation() { result = this.(NodeImpl).getLocationImpl() }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [Locations](https://codeql.github.com/docs/writing-codeql-queries/providing-locations-in-codeql-queries/).
   */
  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    this.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }

  /**
   * Gets a local source node from which data may flow to this node in zero or
   * more local data-flow steps.
   */
  LocalSourceNode getALocalSource() { result.flowsTo(this) }

  /**
   * Gets a data flow node from which data may flow to this node in one local step.
   */
  Node getAPredecessor() { localFlowStep(result, this) }

  /**
   * Gets a data flow node to which data may flow from this node in one local step.
   */
  Node getASuccessor() { localFlowStep(this, result) }

  /** Gets the constant value of this expression, if any. */
  ConstantValue getConstantValue() { result = asExpr().getExpr().getConstantValue() }

  /**
   * Gets the callable corresponding to this block, lambda expression, or call to `proc` or `lambda`.
   *
   * For example, gets the callable in each of the following cases:
   * ```rb
   * { |x| x }        # block expression
   * ->(x) { x }      # lambda expression
   * proc { |x| x }   # call to 'proc'
   * lambda { |x| x } # call to 'lambda'
   * ```
   */
  pragma[noinline]
  CallableNode asCallable() {
    result = this
    or
    exists(CallNode call |
      call.getReceiver().asExpr().getExpr() instanceof SelfVariableAccess and
      call.getMethodName() = ["proc", "lambda"] and
      call.getBlock() = result and
      this = call
    )
  }
}

/** A data-flow node corresponding to a call in the control-flow graph. */
class CallNode extends LocalSourceNode, ExprNode {
  private CfgNodes::ExprNodes::CallCfgNode node;

  CallNode() { node = this.getExprNode() }

  /** Gets the data-flow node corresponding to the receiver of the call corresponding to this data-flow node */
  ExprNode getReceiver() { result.getExprNode() = node.getReceiver() }

  /** Gets the data-flow node corresponding to the `n`th argument of the call corresponding to this data-flow node */
  ExprNode getArgument(int n) { result.getExprNode() = node.getArgument(n) }

  /** Gets the data-flow node corresponding to the named argument of the call corresponding to this data-flow node */
  ExprNode getKeywordArgument(string name) { result.getExprNode() = node.getKeywordArgument(name) }

  /**
   * Gets the `n`th positional argument of this call.
   * Unlike `getArgument`, this excludes keyword arguments.
   */
  final ExprNode getPositionalArgument(int n) {
    result.getExprNode() = node.getPositionalArgument(n)
  }

  /** Gets the name of the method called by the method call (if any) corresponding to this data-flow node */
  string getMethodName() { result = node.getExpr().(MethodCall).getMethodName() }

  /** Gets the number of arguments of this call. */
  int getNumberOfArguments() { result = node.getNumberOfArguments() }

  /** Gets the block of this call. */
  Node getBlock() { result.asExpr() = node.getBlock() }

  /**
   * Gets the data-flow node corresponding to the named argument of the call
   * corresponding to this data-flow node, also including values passed with (pre Ruby
   * 2.0) hash arguments.
   *
   * Such hash arguments are tracked back to their source location within functions, but
   * no inter-procedural analysis occurs.
   *
   * This means all 3 variants below will be handled by this predicate:
   *
   * ```ruby
   * foo(..., some_option: 42)
   * foo(..., { some_option: 42 })
   * options = { some_option: 42 }
   * foo(..., options)
   * ```
   */
  Node getKeywordArgumentIncludeHashArgument(string name) {
    // to reduce number of computed tuples, I have put bindingset on both this and name,
    // meaning we only do the local backwards tracking for known calls and known names.
    // (not because a performance problem was seen, it just seemed right).
    result = this.getKeywordArgument(name)
    or
    exists(CfgNodes::ExprNodes::PairCfgNode pair |
      pair =
        this.getArgument(_)
            .getALocalSource()
            .asExpr()
            .(CfgNodes::ExprNodes::HashLiteralCfgNode)
            .getAKeyValuePair() and
      pair.getKey().getConstantValue().isStringlikeValue(name) and
      result.asExpr() = pair.getValue()
    )
  }
}

/**
 * A call to a setter method.
 *
 * For example,
 * ```rb
 * self.foo = 10
 * a[0] = 10
 * ```
 */
class SetterCallNode extends CallNode {
  SetterCallNode() { asExpr().getExpr() instanceof SetterMethodCall }

  /**
   * Gets the name of the method being called without the trailing `=`. For example, in the following
   * two statements the target name is `value`:
   * ```rb
   * foo.value=(1)
   * foo.value = 1
   * ```
   */
  final string getTargetName() { result = asExpr().getExpr().(SetterMethodCall).getTargetName() }
}

/**
 * An expression, viewed as a node in a data flow graph.
 *
 * Note that because of control-flow splitting, one `Expr` may correspond
 * to multiple `ExprNode`s, just like it may correspond to multiple
 * `ControlFlow::Node`s.
 */
class ExprNode extends Node, TExprNode {
  private CfgNodes::ExprCfgNode n;

  ExprNode() { this = TExprNode(n) }

  /** Gets the expression corresponding to this node. */
  CfgNodes::ExprCfgNode getExprNode() { result = n }
}

/**
 * The value of a parameter at function entry, viewed as a node in a data
 * flow graph.
 */
class ParameterNode extends Node, TParameterNode instanceof ParameterNodeImpl {
  /** Gets the parameter corresponding to this node, if any. */
  final Parameter getParameter() { result = super.getParameter() }
}

/**
 * A data-flow node that is a source of local flow.
 */
class LocalSourceNode extends Node {
  LocalSourceNode() { isLocalSourceNode(this) }

  /** Holds if this `LocalSourceNode` can flow to `nodeTo` in one or more local flow steps. */
  pragma[inline]
  predicate flowsTo(Node nodeTo) { hasLocalSource(nodeTo, this) }

  /**
   * Gets a node that this node may flow to using one heap and/or interprocedural step.
   *
   * See `TypeTracker` for more details about how to use this.
   */
  pragma[inline]
  LocalSourceNode track(TypeTracker t2, TypeTracker t) { t = t2.step(this, result) }

  /**
   * Gets a node that may flow into this one using one heap and/or interprocedural step.
   *
   * See `TypeBackTracker` for more details about how to use this.
   */
  pragma[inline]
  LocalSourceNode backtrack(TypeBackTracker t2, TypeBackTracker t) { t2 = t.step(result, this) }

  /**
   * Gets a node to which data may flow from this node in zero or
   * more local data-flow steps.
   */
  pragma[inline]
  Node getALocalUse() { hasLocalSource(result, this) }

  /** Gets a method call where this node flows to the receiver. */
  CallNode getAMethodCall() { Cached::hasMethodCall(this, result, _) }

  /** Gets a call to a method named `name`, where this node flows to the receiver. */
  CallNode getAMethodCall(string name) { Cached::hasMethodCall(this, result, name) }

  /** Gets a call `obj.name` with no arguments, where this node flows to `obj`. */
  CallNode getAnAttributeRead(string name) {
    result = this.getAMethodCall(name) and
    result.getNumberOfArguments() = 0
  }

  /**
   * Gets a value assigned to `name` on this object, such as the `x` in `obj.name = x`.
   *
   * Concretely, this gets the argument of any call to `name=` where this node flows to the receiver.
   */
  Node getAnAttributeWriteValue(string name) {
    result = this.getAMethodCall(name + "=").getArgument(0)
  }

  /**
   * Gets an access to an element on this node, such as `obj[key]`.
   *
   * Concretely this gets a call to `[]` with 1 argument, where this node flows to the receiver.
   */
  CallNode getAnElementRead() {
    result = this.getAMethodCall("[]") and result.getNumberOfArguments() = 1
  }

  /**
   * Gets an access to the element `key` on this node, such as `obj[:key]`.
   *
   * Concretely this gets a call to `[]` where this node flows to the receiver
   * and the first and only argument has the constant value `key`.
   */
  CallNode getAnElementRead(ConstantValue key) {
    result = this.getAnElementRead() and
    key = result.getArgument(0).getConstantValue()
  }

  /**
   * Gets a value stored as an element on this node, such as the `x` in `obj[key] = x`.
   *
   * Concretely, this gets the second argument from any call to `[]=` where this node flows to the receiver.
   */
  Node getAnElementWriteValue() {
    exists(CallNode call |
      call = this.getAMethodCall("[]=") and
      call.getNumberOfArguments() = 2 and
      result = call.getArgument(1)
    )
  }

  /**
   * Gets the `x` in `obj[key] = x`, where this node flows to `obj`.
   *
   * Concretely, this gets the second argument from any call to `[]=` where this node flows to the receiver
   * and the first argument has constant value `key`.
   */
  Node getAnElementWriteValue(ConstantValue key) {
    exists(CallNode call |
      call = this.getAMethodCall("[]=") and
      call.getNumberOfArguments() = 2 and
      call.getArgument(0).getConstantValue() = key and
      result = call.getArgument(1)
    )
  }
}

/**
 * A node associated with an object after an operation that might have
 * changed its state.
 *
 * This can be either the argument to a callable after the callable returns
 * (which might have mutated the argument), or the qualifier of a field after
 * an update to the field.
 *
 * Nodes corresponding to AST elements, for example `ExprNode`, usually refer
 * to the value before the update.
 */
class PostUpdateNode extends Node instanceof PostUpdateNodeImpl {
  /** Gets the node before the state update. */
  Node getPreUpdateNode() { result = super.getPreUpdateNode() }
}

cached
private module Cached {
  cached
  predicate hasLocalSource(Node sink, Node source) {
    // Declaring `source` to be a `SourceNode` currently causes a redundant check in the
    // recursive case, so instead we check it explicitly here.
    source = sink and
    source instanceof LocalSourceNode
    or
    exists(Node mid |
      hasLocalSource(mid, source) and
      localFlowStepTypeTracker(mid, sink)
    )
  }

  cached
  predicate hasMethodCall(LocalSourceNode source, CallNode call, string name) {
    source.flowsTo(call.getReceiver()) and
    call.getMethodName() = name
  }

  cached
  predicate hasYieldCall(BlockParameterNode block, CallNode yield) {
    exists(MethodBase method, YieldCall call |
      block.getMethod() = method and
      call.getEnclosingMethod() = method and
      yield.asExpr().getExpr() = call
    )
  }
}

private import Cached

/** Gets a node corresponding to expression `e`. */
ExprNode exprNode(CfgNodes::ExprCfgNode e) { result.getExprNode() = e }

/**
 * Gets the node corresponding to the value of parameter `p` at function entry.
 */
ParameterNode parameterNode(Parameter p) { result.getParameter() = p }

/**
 * Holds if data flows from `nodeFrom` to `nodeTo` in exactly one local
 * (intra-procedural) step.
 */
predicate localFlowStep = localFlowStepImpl/2;

/**
 * Holds if data flows from `source` to `sink` in zero or more local
 * (intra-procedural) steps.
 */
pragma[inline]
predicate localFlow(Node source, Node sink) { localFlowStep*(source, sink) }

/**
 * Holds if data can flow from `e1` to `e2` in zero or more
 * local (intra-procedural) steps.
 */
pragma[inline]
predicate localExprFlow(CfgNodes::ExprCfgNode e1, CfgNodes::ExprCfgNode e2) {
  localFlow(exprNode(e1), exprNode(e2))
}

/** A reference contained in an object. */
class Content extends TContent {
  /** Gets a textual representation of this content. */
  string toString() { none() }

  /** Gets the location of this content. */
  Location getLocation() { none() }
}

/** Provides different sub classes of `Content`. */
module Content {
  /** An element in a collection, for example an element in an array or in a hash. */
  class ElementContent extends Content, TElementContent { }

  /** An element in a collection at a known index. */
  class KnownElementContent extends ElementContent, TKnownElementContent {
    private ConstantValue cv;

    KnownElementContent() { this = TKnownElementContent(cv) }

    /** Gets the index in the collection. */
    ConstantValue getIndex() { result = cv }

    override string toString() { result = "element " + cv }
  }

  /** An element in a collection at an unknown index. */
  class UnknownElementContent extends ElementContent, TUnknownElementContent {
    override string toString() { result = "element" }
  }

  /** A field of an object, for example an instance variable. */
  class FieldContent extends Content, TFieldContent {
    private string name;

    FieldContent() { this = TFieldContent(name) }

    /** Gets the name of the field. */
    string getName() { result = name }

    override string toString() { result = name }
  }

  /** Gets the element content corresponding to constant value `cv`. */
  ElementContent getElementContent(ConstantValue cv) {
    result = TKnownElementContent(cv)
    or
    not exists(TKnownElementContent(cv)) and
    result = TUnknownElementContent()
  }

  /**
   * Gets the constant value of `e`, which corresponds to a valid known
   * element index. Unlike calling simply `e.getConstantValue()`, this
   * excludes negative array indices.
   */
  ConstantValue getKnownElementIndex(Expr e) {
    result = getElementContent(e.getConstantValue()).(KnownElementContent).getIndex()
  }

  /**
   * A value stored behind a getter/setter pair.
   *
   * This is used (only) by type-tracking, as a heuristic since getter/setter pairs tend to operate
   * on similar types of objects (i.e. the type flowing into a setter will likely flow out of the getter).
   */
  class AttributeNameContent extends Content, TAttributeName {
    private string name;

    AttributeNameContent() { this = TAttributeName(name) }

    override string toString() { result = "attribute " + name }

    /** Gets the attribute name. */
    string getName() { result = name }
  }

  /** Gets `AttributeNameContent` of the given name. */
  AttributeNameContent getAttributeName(string name) { result.getName() = name }
}

/**
 * An entity that represents a set of `Content`s.
 *
 * The set may be interpreted differently depending on whether it is
 * stored into (`getAStoreContent`) or read from (`getAReadContent`).
 */
class ContentSet extends TContentSet {
  /** Holds if this content set is the singleton `{c}`. */
  predicate isSingleton(Content c) { this = TSingletonContent(c) }

  /** Holds if this content set represents all `ElementContent`s. */
  predicate isAnyElement() { this = TAnyElementContent() }

  /**
   * Holds if this content set represents a specific known element index, or an
   * unknown element index.
   */
  predicate isKnownOrUnknownElement(Content::KnownElementContent c) {
    this = TKnownOrUnknownElementContent(c)
  }

  /**
   * Holds if this content set represents all `KnownElementContent`s where
   * the index is an integer greater than or equal to `lower`.
   */
  predicate isElementLowerBound(int lower) { this = TElementLowerBoundContent(lower, false) }

  /**
   * Holds if this content set represents `UnknownElementContent` unioned with
   * all `KnownElementContent`s where the index is an integer greater than or
   * equal to `lower`.
   */
  predicate isElementLowerBoundOrUnknown(int lower) {
    this = TElementLowerBoundContent(lower, true)
  }

  /** Gets a textual representation of this content set. */
  string toString() {
    exists(Content c |
      this.isSingleton(c) and
      result = c.toString()
    )
    or
    this.isAnyElement() and
    result = "any element"
    or
    exists(Content::KnownElementContent c |
      this.isKnownOrUnknownElement(c) and
      result = c + " or unknown"
    )
    or
    exists(int lower, boolean includeUnknown |
      this = TElementLowerBoundContent(lower, includeUnknown)
    |
      includeUnknown = false and
      result = lower + "..!"
      or
      includeUnknown = true and
      result = lower + ".."
    )
  }

  /** Gets a content that may be stored into when storing into this set. */
  Content getAStoreContent() {
    this.isSingleton(result)
    or
    // For reverse stores, `a[unknown][0] = x`, it is important that the read-step
    // from `a` to `a[unknown]` (which can read any element), gets translated into
    // a reverse store step that store only into `?`
    this.isAnyElement() and
    result = TUnknownElementContent()
    or
    // For reverse stores, `a[1][0] = x`, it is important that the read-step
    // from `a` to `a[1]` (which can read both elements stored at exactly index `1`
    // and elements stored at unknown index), gets translated into a reverse store
    // step that store only into `1`
    this.isKnownOrUnknownElement(result)
    or
    this.isElementLowerBound(_) and
    result = TUnknownElementContent()
  }

  /** Gets a content that may be read from when reading from this set. */
  Content getAReadContent() {
    this.isSingleton(result)
    or
    this.isAnyElement() and
    result instanceof Content::ElementContent
    or
    exists(Content::KnownElementContent c | this.isKnownOrUnknownElement(c) |
      result = c or
      result = TUnknownElementContent()
    )
    or
    exists(int lower, boolean includeUnknown |
      this = TElementLowerBoundContent(lower, includeUnknown)
    |
      exists(int i |
        result.(Content::KnownElementContent).getIndex().isInt(i) and
        i >= lower
      )
      or
      includeUnknown = true and
      result = TUnknownElementContent()
    )
  }
}

/**
 * Holds if the guard `g` validates the expression `e` upon evaluating to `branch`.
 *
 * The expression `e` is expected to be a syntactic part of the guard `g`.
 * For example, the guard `g` might be a call `isSafe(x)` and the expression `e`
 * the argument `x`.
 */
signature predicate guardChecksSig(CfgNodes::ExprCfgNode g, CfgNode e, boolean branch);

/**
 * Provides a set of barrier nodes for a guard that validates an expression.
 *
 * This is expected to be used in `isBarrier`/`isSanitizer` definitions
 * in data flow and taint tracking.
 */
module BarrierGuard<guardChecksSig/3 guardChecks> {
  pragma[nomagic]
  private predicate guardChecksSsaDef(CfgNodes::ExprCfgNode g, boolean branch, Ssa::Definition def) {
    guardChecks(g, def.getARead(), branch)
  }

  pragma[nomagic]
  private predicate guardControlsSsaDef(
    CfgNodes::ExprCfgNode g, boolean branch, Ssa::Definition def, Node n
  ) {
    def.getARead() = n.asExpr() and
    guardControlsBlock(g, n.asExpr().getBasicBlock(), branch)
  }

  /** Gets a node that is safely guarded by the given guard check. */
  Node getABarrierNode() {
    exists(CfgNodes::ExprCfgNode g, boolean branch, Ssa::Definition def |
      guardChecksSsaDef(g, branch, def) and
      guardControlsSsaDef(g, branch, def, result)
    )
    or
    result.asExpr() = getAMaybeGuardedCapturedDef().getARead()
  }

  /**
   * Gets an implicit entry definition for a captured variable that
   * may be guarded, because a call to the capturing callable is guarded.
   *
   * This is restricted to calls where the variable is captured inside a
   * block.
   */
  private Ssa::Definition getAMaybeGuardedCapturedDef() {
    exists(
      CfgNodes::ExprCfgNode g, boolean branch, CfgNodes::ExprCfgNode testedNode,
      Ssa::Definition def, CfgNodes::ExprNodes::CallCfgNode call
    |
      def.getARead() = testedNode and
      guardChecks(g, testedNode, branch) and
      SsaImpl::captureFlowIn(call, def, result) and
      guardControlsBlock(g, call.getBasicBlock(), branch) and
      result.getBasicBlock().getScope() = call.getExpr().(MethodCall).getBlock()
    )
  }
}

/** Holds if the guard `guard` controls block `bb` upon evaluating to `branch`. */
private predicate guardControlsBlock(CfgNodes::ExprCfgNode guard, BasicBlock bb, boolean branch) {
  exists(ConditionBlock conditionBlock, SuccessorTypes::BooleanSuccessor s |
    guard = conditionBlock.getLastNode() and
    s.getValue() = branch and
    conditionBlock.controls(bb, s)
  )
}

/**
 * A guard that validates some expression.
 *
 * To use this in a configuration, extend the class and provide a
 * characteristic predicate precisely specifying the guard, and override
 * `checks` to specify what is being validated and in which branch.
 *
 * It is important that all extending classes in scope are disjoint.
 */
abstract deprecated class BarrierGuard extends CfgNodes::ExprCfgNode {
  private ConditionBlock conditionBlock;

  BarrierGuard() { this = conditionBlock.getLastNode() }

  /** Holds if this guard controls block `b` upon evaluating to `branch`. */
  private predicate controlsBlock(BasicBlock bb, boolean branch) {
    exists(SuccessorTypes::BooleanSuccessor s | s.getValue() = branch |
      conditionBlock.controls(bb, s)
    )
  }

  /**
   * Holds if this guard validates `expr` upon evaluating to `branch`.
   * For example, the following code validates `foo` when the condition
   * `foo == "foo"` is true.
   * ```ruby
   * if foo == "foo"
   *   do_something
   *  else
   *   do_something_else
   * end
   * ```
   */
  abstract predicate checks(CfgNode expr, boolean branch);

  /**
   * Gets an implicit entry definition for a captured variable that
   * may be guarded, because a call to the capturing callable is guarded.
   *
   * This is restricted to calls where the variable is captured inside a
   * block.
   */
  private Ssa::Definition getAMaybeGuardedCapturedDef() {
    exists(
      boolean branch, CfgNodes::ExprCfgNode testedNode, Ssa::Definition def,
      CfgNodes::ExprNodes::CallCfgNode call
    |
      def.getARead() = testedNode and
      this.checks(testedNode, branch) and
      SsaImpl::captureFlowIn(call, def, result) and
      this.controlsBlock(call.getBasicBlock(), branch) and
      result.getBasicBlock().getScope() = call.getExpr().(MethodCall).getBlock()
    )
  }

  final Node getAGuardedNode() {
    exists(boolean branch, CfgNodes::ExprCfgNode testedNode, Ssa::Definition def |
      def.getARead() = testedNode and
      def.getARead() = result.asExpr() and
      this.checks(testedNode, branch) and
      this.controlsBlock(result.asExpr().getBasicBlock(), branch)
    )
    or
    result.asExpr() = this.getAMaybeGuardedCapturedDef().getARead()
  }
}

/**
 * A representation of a run-time module or class.
 *
 * This is equivalent to the type `Ast::Module` but provides data-flow specific methods.
 */
class ModuleNode instanceof Module {
  /** Gets a declaration of this module, if any. */
  final ModuleBase getADeclaration() { result = super.getADeclaration() }

  /** Gets the super class of this module, if any. */
  final ModuleNode getSuperClass() { result = super.getSuperClass() }

  /** Gets an immediate sub class of this module, if any. */
  final ModuleNode getASubClass() { result = super.getASubClass() }

  /** Gets a `prepend`ed module. */
  final ModuleNode getAPrependedModule() { result = super.getAPrependedModule() }

  /** Gets an `include`d module. */
  final ModuleNode getAnIncludedModule() { result = super.getAnIncludedModule() }

  /** Gets the super class or an included or prepended module. */
  final ModuleNode getADirectAncestor() { result = super.getADirectAncestor() }

  /** Gets a direct subclass or module including or prepending this one. */
  final ModuleNode getADirectDescendent() { result = super.getADirectDescendent() }

  /** Gets a module that is transitively subclassed, included, or prepended by this module. */
  final ModuleNode getAnAncestor() { result = super.getAnAncestor() }

  /** Gets a module that transitively subclasses, includes, or prepends this module. */
  final ModuleNode getADescendent() { result = super.getADescendent() }
  /** Holds if this module is a class. */
  predicate isClass() { super.isClass() }

  /** Gets a textual representation of this module. */
  final string toString() { result = super.toString() }

  /**
   * Gets the qualified name of this module, if any.
   *
   * Only modules that can be resolved will have a qualified name.
   */
  final string getQualifiedName() { result = super.getQualifiedName() }

  /** Gets the location of this module. */
  final Location getLocation() { result = super.getLocation() }

  /**
   * Gets `self` in a declaration of this module.
   *
   * This only gets `self` at the module level, not inside any (singleton) method.
   */
  LocalSourceNode getModuleLevelSelf() {
    result.(SsaDefinitionNode).getVariable() = super.getADeclaration().getModuleSelfVariable()
  }

  /**
   * Gets `self` in the module declaration or in one of its singleton methods.
   *
   * Does not take inheritance into account.
   */
  LocalSourceNode getAModuleSelf() {
    result = this.getModuleLevelSelf()
    or
    result = this.getASingletonMethod().getSelfParameter()
  }

  /**
   * Gets a call to method `name` on `self` in the module-level scope of this module (not in a method).
   *
   * For example,
   * ```rb
   * module M
   *   include A  # getAModuleLevelCall("include")
   *   foo :bar   # getAModuleLevelCall("foo")
   * end
   * ```
   */
  CallNode getAModuleLevelCall(string name) {
    result = this.getModuleLevelSelf().getAMethodCall(name) and
    not this.getQualifiedName() = "Object" // do not include top-levels
  }

  /** Gets a constant or `self` variable that refers to this module. */
  LocalSourceNode getAnImmediateReference() {
    result.asExpr().getExpr() = super.getAnImmediateReference()
  }

  /**
   * Gets a singleton method declared in this module (or in a singleton class
   * augmenting this module).
   *
   * Does not take inheritance into account.
   */
  MethodNode getASingletonMethod() { result.asMethod() = super.getASingletonMethod() }

  /**
   * Gets the singleton method named `name` declared in this module (or in a singleton class
   * augmenting this module).
   *
   * Does not take inheritance into account.
   */
  MethodNode getSingletonMethod(string name) {
    result = this.getASingletonMethod() and
    result.getMethodName() = name
  }

  /**
   * Gets an instance method declared in this module.
   *
   * Does not take inheritance into account.
   */
  MethodNode getAnInstanceMethod() {
    result.asMethod() = this.getADeclaration().getAMethod().(Method)
  }

  /**
   * Gets an instance method named `name` declared in this module.
   *
   * Does not take inheritance into account.
   */
  MethodNode getInstanceMethod(string name) {
    result = this.getAnInstanceMethod() and
    result.getMethodName() = name
  }

  /**
   * Gets the `self` parameter of an instance method declared in this module.
   *
   * Does not take inheritance into account.
   */
  ParameterNode getAnInstanceSelf() {
    result = TSelfParameterNode(this.getAnInstanceMethod().asMethod())
  }

  private InstanceVariableAccess getAnInstanceVariableAccess(string name) {
    exists(InstanceVariable v |
      v.getDeclaringScope() = this.getAnInstanceMethod().asMethod() and
      v.getName() = name and
      result.getVariable() = v
    )
  }

  /**
   * Gets an access to the instance variable `name` in this module.
   *
   * Does not take inheritance into account.
   */
  LocalSourceNode getAnInstanceVariableRead(string name) {
    result.asExpr().getExpr() = this.getAnInstanceVariableAccess(name).(InstanceVariableReadAccess)
  }

  /**
   * Gets the right-hand side of an assignment to the instance variable `name` in this module.
   *
   * Does not take inheritance into account.
   */
  Node getAnInstanceVariableWriteValue(string name) {
    exists(Assignment assignment |
      assignment.getLeftOperand() = this.getAnInstanceVariableAccess(name) and
      result.asExpr().getExpr() = assignment.getRightOperand()
    )
  }

  /**
   * Gets the enclosing module, as it appears in the qualified name of this module.
   *
   * For example, the canonical enclosing module of `A::B` is `A`, and `A` itself has no canonical enclosing module.
   */
  ModuleNode getCanonicalEnclosingModule() { result = super.getCanonicalEnclosingModule() }

  /**
   * Gets a module named `name` declared inside this one (not aliased), provided
   * that such a module is defined or reopened in the current codebase.
   *
   * For example, for `A::B` the canonical nested module named `C` would be `A::B::C`.
   *
   * Note that this is not the same as constant lookup. If `A::B::C` would resolve to a
   * module whose qualified name is not `A::B::C`, then it will not be found by
   * this predicate.
   */
  ModuleNode getCanonicalNestedModule(string name) { result = super.getCanonicalNestedModule(name) }
}

/**
 * A representation of a run-time class.
 */
class ClassNode extends ModuleNode {
  ClassNode() { isClass() }
}

/**
 * A data flow node corresponding to a method, block, or lambda expression.
 */
class CallableNode extends ExprNode {
  private Callable callable;

  CallableNode() { this.asExpr().getExpr() = callable }

  /** Gets the underlying AST node as a `Callable`. */
  Callable asCallableAstNode() { result = callable }

  private ParameterPosition getParameterPosition(ParameterNodeImpl node) {
    node.isSourceParameterOf(callable, result)
  }

  /** Gets the `n`th positional parameter. */
  ParameterNode getParameter(int n) { getParameterPosition(result).isPositional(n) }

  /** Gets the keyword parameter of the given name. */
  ParameterNode getKeywordParameter(string name) { getParameterPosition(result).isKeyword(name) }

  /** Gets the `self` parameter of this callable, if any. */
  ParameterNode getSelfParameter() { getParameterPosition(result).isSelf() }

  /**
   * Gets the `hash-splat` parameter. This is a synthetic parameter holding
   * a hash object with entries for each keyword argument passed to the function.
   */
  ParameterNode getHashSplatParameter() { getParameterPosition(result).isHashSplat() }

  /**
   * Gets the block parameter of this method, if any.
   */
  ParameterNode getBlockParameter() { getParameterPosition(result).isBlock() }

  /**
   * Gets a `yield` in this method call or `.call` on the block parameter.
   */
  CallNode getABlockCall() {
    hasYieldCall(getBlockParameter(), result)
    or
    result = getBlockParameter().getAMethodCall("call")
  }

  /**
   * Gets the canonical return node from this callable.
   *
   * Each callable has exactly one such node, and its location may not correspond
   * to any particular return site - consider using `getAReturningNode` to get nodes
   * whose locations correspond to return sites.
   */
  Node getReturn() { result.(SynthReturnNode).getCfgScope() = callable }

  /**
   * Gets a data flow node whose value is about to be returned by this callable.
   */
  Node getAReturningNode() { result = this.getReturn().(SynthReturnNode).getAnInput() }
}

/**
 * A data flow node corresponding to a method (possibly a singleton method).
 */
class MethodNode extends CallableNode {
  MethodNode() { super.asCallableAstNode() instanceof MethodBase }

  /** Gets the underlying AST node for this method. */
  MethodBase asMethod() { result = this.asCallableAstNode() }

  /** Gets the name of this method. */
  string getMethodName() { result = asMethod().getName() }
}

/**
 * A data flow node corresponding to a block argument.
 */
class BlockNode extends CallableNode {
  BlockNode() { super.asCallableAstNode() instanceof Block }

  /** Gets the underlying AST node for this block. */
  Block asBlock() { result = this.asCallableAstNode() }
}
