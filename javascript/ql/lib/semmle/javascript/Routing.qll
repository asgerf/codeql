/**
 * A model of routing trees, describing the composition of route handlers and middleware functions
 * in a web server application. See `Routing::Node` for more details.
 */

private import javascript
private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps
private import semmle.javascript.dataflow.internal.StepSummary

/**
 * A model of routing trees, describing the composition of route handlers and middleware functions
 * in a web server application. See `Routing::Node` for more details.
 */
module Routing {
  /**
   * A node in a routing tree modelling the composition of middleware functions and route handlers.
   *
   * More precisely, this is a node in a graph representing a set of possible routing trees, as the
   * concrete shape of the  routing tree may be depend on branching control flow.
   *
   * Each node represents a function that can receive an incoming request, though not necessarily
   * a function with an explicit body in the source code.
   *
   * A node may either consume the request, dispatching to its first child, or pass it on to its successor
   * in the tree. The successor is the next sibling, or in case there is no next sibling, it is the next sibling
   * of the first ancestor that has a next sibling.
   */
  class Node extends DataFlow::Node instanceof Node::Range {
    /**
     * Gets the next sibling of this node in the routing tree.
     */
    final Node getNextSibling() { any(Node::Range parent).hasSiblingChildren(this, result) }

    /**
     * Gets the previous sibling of this node in the routing tree.
     */
    final Node getPreviousSibling() { any(Node::Range parent).hasSiblingChildren(result, this) }

    /**
     * Gets a child of this node in the routing tree.
     */
    final Node getAChild() {
      result = getLastChild()
      or
      result = getAChild().getPreviousSibling()
    }

    /**
     * Gets the parent of this node in the routing tree.
     */
    final Node getParent() { result.getAChild() = this }

    /**
     * Gets the first child of this node in the routing tree.
     */
    final Node getFirstChild() {
      result = getAChild() and
      not exists(result.getPreviousSibling())
    }

    /**
     * Gets the last child of this node in the routing tree.
     */
    final Node getLastChild() { result = super.getLastChild() }

    /**
     * Gets the root node of this node in the routing tree.
     */
    final RootNode getRootNode() { this = result.getADescendant() }

    /**
     * Holds if this node may invoke its continuation, that is, the
     * incoming request may be passed on to the successor.
     */
    predicate mayInvokeContinuation() {
      getLastChild().mayInvokeContinuation()
      or
      not exists(getLastChild()) and
      not this instanceof RouteHandler
      or
      exists(this.(RouteHandler).getAContinuationInvocation())
    }

    /** Gets the parent of this node, provided that this node may invoke its continuation. */
    private Node getContinuationParent() {
      result = getParent() and
      result.mayInvokeContinuation()
    }

    /**
     * Gets a path prefix to be matched against the path of incoming requests.
     *
     * If the prefix matches, the request is dispatched to the first child, with a modified path
     * where the matched prefix has been removed. For example, if the prefix is `/foo` and the incoming
     * request has path `/foo/bar`, a request with path `/bar` is dispatched to the first child.
     *
     * If the prefix does not match, the request is passed on to the continuation.
     */
    final string getRelativePath() {
      result = super.getRelativePath()
    }

    /**
     * Gets the path prefix needed to reach this node from the given ancestor, that is, the concatenation
     * of all relative paths between this node and the ancestor.
     *
     * To restrict the size of the predicate, this is only available for the ancestors that are "fork" nodes,
     * that is, a node that has siblings (i.e. multiple children).
     */
    private string getPathFromFork(Node fork) {
      super.hasSiblingChildren(_, _) and
      this = fork and
      result = ""
      or
      exists(Node parent | parent = getParent() |
        not exists(parent.getRelativePath()) and
        result = parent.getPathFromFork(fork)
        or
        result = parent.getPathFromFork(fork) + parent.getRelativePath() and
        result.length() < 100
      )
    }

    /**
     * Gets an HTTP method required to reach this node from the given ancestor, or `*` if any method
     * can be used.
     *
     * To restrict the size of the predicate, this is only available for the ancestors that are "fork" nodes,
     * that is, a node that has siblings (i.e. multiple children).
     */
    private string getHttpMethodFromFork(Node fork) {
      super.hasSiblingChildren(_, _) and
      this = fork and
      (
        result = super.getHttpMethod()
        or
        not exists(super.getHttpMethod()) and
        result = "*"
      )
      or
      result = getParent().getHttpMethodFromFork(fork) and
      (
        // Only the ancestor restricts the HTTP method
        not exists(super.getHttpMethod())
        or
        // Intersect permitted HTTP methods
        result = super.getHttpMethod()
      )
      or
      // The ancestor allows any HTTP method, but this node restricts it
      getParent().getHttpMethodFromFork(fork) = "*" and
      result = super.getHttpMethod()
    }

    /**
     * Holds if `node` has processed the incoming request strictly prior to this node.
     */
    pragma[inline]
    predicate isGuardedBy(Node node) {
      exists(Node base1, Node base2, Node fork |
        base1 = pragma[only_bind_out](node).getContinuationParent*() and
        base2 = base1.getNextSibling+() and
        this = base2.getAChild*() and
        fork = base1.getParent() and
        isEitherPrefixOfTheOther(getPathFromFork(fork), node.getPathFromFork(fork)) and
        areHttpMethodsMatching(base1.getHttpMethodFromFork(fork), base2.getHttpMethodFromFork(fork))
      )
    }

    /**
     * Gets an HTTP method name which this node will accept, or nothing if the node accepts all HTTP methods, not
     * taking into account the context from ancestors or children nodes.
     */
    HTTP::RequestMethodName getOwnHttpMethod() {
      result = super.getHttpMethod()
    }
  }

  /** Holds if `a` is a prefix of `b` or the other way around. */
  bindingset[a, b]
  private predicate isEitherPrefixOfTheOther(string a, string b) {
    a = b + any(string s) or b = a + any(string s)
  }

  /** Holds if `a` and `b` are the same HTTP method name or either of them is `*`. */
  bindingset[a, b]
  private predicate areHttpMethodsMatching(string a, string b) {
    a = "*" or b = "*" or a = b
  }


  /**
   * Companion module to the `Node` class, containing abstract classes
   * that can be used to extend the routing model.
   */
  module Node {
    /**
     * A node in the routing tree.
     *
     * This class can be extended to contribute new kinds of nodes to tree,
     * though in common cases it is preferrable to extend one of the more specialized classes:
     * - `Routing::Node::UseSite` to mark values that are used as a route handler,
     * - `Routing::Node::WithArguments` for nodes with an indexed sequence of children,
     * - `Routing::RouteSetup::MethodCall` for nodes manipulating a router object
     */
    abstract class Range extends DataFlow::Node {
      /** Gets the last child of this node, if it has any children. */
      Routing::Node getLastChild() { none() }

      /** Holds if `pred` and `succ` are adjacent siblings, in that order. */
      predicate hasSiblingChildren(Routing::Node pred, Routing::Node succ) { none() }

      /**
       * Gets a node whose value can be accessed via the given access path on `n`th route handler input,
       * from any route handler that follows after this one.
       *
       * For example, in the context of Express, the `app` object is available as `req.app`:
       * ```js
       * app.get('/', (req, res) => {
       *   req.app; // alias for 'app'
       * })
       * ```
       * This can be modelled by mapping `(0, "app")` to the `app` data-flow node (`n=0` corresponds
       * to the `req` parameter).
       */
      DataFlow::Node getValueAtAccessPath(int n, string path) { none() }

      /**
       * Gets a path prefix to be matched against the path of incoming requests.
       *
       * If the prefix matches, the request is dispatched to the first child, with a modified path
       * where the matched prefix has been removed. For example, if the prefix is `/foo` and the incoming
       * request has path `/foo/bar`, a request with path `/bar` is dispatched to the first child.
       *
       * If the prefix does not match, the request is passed on to the continuation.
       */
      string getRelativePath() { none() }

      /**
       * Gets an HTTP request method name (in upper case) matched by this node, or nothing
       * if all HTTP request method names are accepted.
       */
      HTTP::RequestMethodName getHttpMethod() { none() }
    }

    private StepSummary routeStepSummary() {
      // Do not allow call steps as they lead to loss of context.
      // Such steps are usually handled by the 'ImpliedRouteHandler' class.
      result = LevelStep() or result = ReturnStep()
    }

    /**
     * A node that is used as a route handler.
     *
     * Values that flow to this use site are themselves considered use sites, and are
     * considered children of this one. (Intuitively, requests dispatched to this use-site
     * are delagated to any node that flows here.)
     *
     * Framework models may extend this class to mark nodes as being use sites.
     */
    abstract class UseSite extends Range {
      private DataFlow::Node getRawSource() {
        result = getALocalSource()
        or
        StepSummary::smallstep(result, this, routeStepSummary())
        or
        HTTP::routeHandlerStep(result, this)
        or
        exists(string prop |
          StepSummary::smallstep(result, getSourceProp(prop).getALocalUse(), StoreStep(prop))
        )
      }

      /** Gets a node that flows to this use site. */
      DataFlow::Node getSource() {
        // If an alias for a router flows here, make sure we use the router as the source
        result = getRawSource() and
        not result = any(RouteSetup::Range r).getARouterAlias(_)
        or
        getRawSource() = getARouterRef(result)
      }

      /** Gets a node whose `prop` property flows to this use site. */
      private DataFlow::SourceNode getSourceProp(string prop) {
        StepSummary::step(result, this, LoadStep(prop))
        or
        StepSummary::step(result, getSourceProp(prop), routeStepSummary())
        or
        StepSummary::step(result, getSourceProp(prop), CopyStep(prop))
        or
        exists(string oldProp |
          StepSummary::step(result, getSourceProp(oldProp), LoadStoreStep(prop, oldProp))
        )
      }

      final override Routing::Node getLastChild() { result = getSource() and result != this }
    }

    /**
     * A node flowing into a use site, modelled as a child of the use site.
     */
    private class UseSiteSource extends UseSite {
      UseSiteSource() { this = any(UseSite use).getSource() }
    }

    /**
     * A node that has a linear sequence of children, which should all be marked as route objects.
     */
    abstract class WithArguments extends Range {
      abstract DataFlow::Node getChild(int n);

      private int getNumChild() { result = strictcount(getChild(_)) }

      final override Routing::Node getLastChild() { result = getChild(getNumChild() - 1) }

      override predicate hasSiblingChildren(Routing::Node pred, Routing::Node succ) {
        exists(int n |
          pred = getChild(n) and
          succ = getChild(n + 1)
        )
      }
    }

    /** An argument to a `WithArguments` instance, seen as a use site. */
    private class Argument extends UseSite {
      Argument() { this = any(WithArguments n).getChild(_) }
    }

    /** An array which has already been determined to a routing node, with children. */
    private class ImpliedArrayRoute extends Node::WithArguments, DataFlow::ArrayCreationNode {
      ImpliedArrayRoute() { this instanceof Node::UseSite }

      override DataFlow::Node getChild(int n) { result = getElement(n) }
    }
  }

  /**
   * A node in the routing tree which has no parent.
   */
  class RootNode extends Node {
    RootNode() { not exists(getParent()) }

    final Node getADescendant() { result = getAChild*() }
  }

  /**
   * A node representing a place where one or more routes are installed onto a mutable
   * router object.
   *
   * The children of this node are the individual route handlers installed here.
   *
   * The siblings of this node are the other route setups locally affecting the same router,
   * in the order in which they are installed.
   *
   * In case of branching control flow, the siblings are non-linear, that is, some route setups
   * will have multiple previous/next siblings, reflecting the different paths the program may take
   * during setup.
   */
  class RouteSetup extends Node {
    RouteSetup() { this instanceof RouteSetup::Range }

    /**
     * Gets the router affected by this route setup.
     *
     * This is an alias for `getParent`, but may be preferred for readability.
     */
    final Node getRouter() { result = getParent() }
  }

  /**
   * Companion module to the `RouteSetup` class, containing classes that can be use to contribute
   * new kinds of route setups.
   */
  module RouteSetup {
    /**
     * This class can be extended to contribute new kinds of route setups.
     */
    abstract class Range extends Node::Range {
      /**
       * Holds if this route setup targets `router` and occurs at the given `cfgNode`.
       */
      abstract predicate isInstalledAt(DataFlow::Node router, ControlFlowNode cfgNode);

      /**
       * Gets a data-flow node that refers to the given `router`.
       *
       * This can be used to model route setups that return the router itself, to support
       * chaining calls.
       */
      DataFlow::SourceNode getARouterAlias(DataFlow::Node router) { none() }
    }

    /**
     * A route setup that is method call on a router object, installing its arguments as route handlers.
     *
     * This class can be extended to contribute new kinds of route handlers.
     */
    abstract class MethodCall extends RouteSetup::Range, Node::WithArguments,
      DataFlow::MethodCallNode {
      override DataFlow::Node getChild(int n) { result = getArgument(n) }

      override predicate isInstalledAt(DataFlow::Node router, ControlFlowNode cfgNode) {
        router = getReceiver() and cfgNode = getEnclosingExpr()
      }

      override DataFlow::SourceNode getARouterAlias(DataFlow::Node router) {
        router = getReceiver() and
        result = this
      }
    }
  }

  /**
   * Gets a node that refers to the given `router` via an alias established by
   * a route setup (usually by the route setup returning `this`).
   */
  private DataFlow::SourceNode getARouterRef(DataFlow::SourceNode router) {
    any(RouteSetup::Range r).isInstalledAt(router.getALocalUse(), _) and
    result = router and
    not result = any(RouteSetup::Range r).getARouterAlias(_) // only track the root alias
    or
    result = any(RouteSetup::Range r).getARouterAlias(getARouterRef(router).getALocalUse())
  }

  /**
   * Like `RouteSetup::Range.isInstalledAt` but with the router mapped to its root alias.
   */
  private predicate isInstalledAt(RouteSetup::Range setup, DataFlow::SourceNode router, ControlFlowNode cfgNode) {
    setup.isInstalledAt(getARouterRef(router).getALocalUse(), cfgNode)
  }

  /** Holds if `router` is the `SourceNode` targeted by some route setup. */
  pragma[nomagic]
  private predicate isRouter(DataFlow::SourceNode router) {
    any(RouteSetup::Range r).isInstalledAt(router.getALocalUse(), _)
  }

  /**
   * Gets the canonical data flow node representing references to `router` in `container`.
   *
   * For captured references to a router object, we use the SSA capture definition node at the function
   * entry point (when such a node exists).
   */
  pragma[nomagic]
  private DataFlow::Node getRouterNodeInContainer(DataFlow::SourceNode router, StmtContainer container) {
    isRouter(router) and
    (
      container = router.getContainer() and
      result = router
      or
      result.getALocalSource() = router and
      exists(SsaVariableCapture capture |
        capture.getBasicBlock() = container.getEntryBB() and
        result = DataFlow::ssaDefinitionNode(capture)
      )
    )
  }

  /**
   * A `Node` generated from the router targeted by a `RouteSetup`.
   */
  private class RouterRange extends Node::Range, DataFlow::Node {
    DataFlow::SourceNode routerSource;

    RouterRange() {
      this = getRouterNodeInContainer(routerSource, _)
    }

    override Node getLastChild() {
      result = getMostRecentRouteSetupAt(routerSource, getContainer().getExit())
    }

    override predicate hasSiblingChildren(Node pred, Node succ) {
      exists(ControlFlowNode cfgNode |
        isInstalledAt(succ, routerSource, cfgNode) and
        pred = getMostRecentRouteSetupAt(routerSource, cfgNode.getAPredecessor())
      )
    }
  }

  /**
   * Gets the route setup most recently performed on `router` at `node`, or in the case of branching control flow,
   * gets any route setup that could be the most recent one.
   */
  private RouteSetup::Range getMostRecentRouteSetupAt(
    DataFlow::SourceNode router, ControlFlowNode node
  ) {
    isInstalledAt(result, router, node)
    or
    result = getMostRecentRouteSetupAt(router, node.getAPredecessor()) and
    not exists(RouteSetup::Range setup | isInstalledAt(setup, router, node))
  }

  /**
   * A call where a mutable router object escapes into a parameter or is returned from a function.
   *
   * This is modelled as a route setup targeting the "local router" value and having
   * the "target router" as its only child.
   *
   * For example,
   * ```js
   * function addMiddleware(r) {
   *   r.use(bodyParser());
   *   r.use(auth());
   * }
   *
   * let app = express();
   * addMiddleware(app); // <-- implied route setup
   * app.get('/', handleRequest);
   * ```
   * here the call to `addMiddleware` is an implied route setup with `app`
   * as the "local router" and `r` as the "target router".
   *
   * The routing tree ends up having the following shape:
   * - `app`
   *   - `addMiddleware(app)`
   *     - `r`
   *       - `r.use()`
   *         - `bodyParser()`
   *       - `r.use()`
   *         - `auth()`
   *   - `app.get(...)`
   *     - `'/'`
   *     - `handleRequest`
   */
  private class ImpliedRouteSetup extends RouteSetup::Range {
    DataFlow::Node localRouter;
    RouterRange targetRouter;

    ImpliedRouteSetup() {
      // Router escaping into parameter: e.g `addMiddlewares(app)`
      DataFlow::argumentPassingStep(this, localRouter, _, targetRouter)
      or
      // Router returned from function: e.g `app.use(getMiddlewares())`
      FlowSteps::returnStep(targetRouter, this) and
      localRouter = this
      or
      // Router captured by inner function, e.g:
      //
      //   app = express();
      //   function addMiddlewares() {
      //     app.use(...);
      //   }
      //   addMiddlewares();
      //
      exists(Function callee, DataFlow::SourceNode router |
        FlowSteps::calls(this, callee) and
        targetRouter = getRouterNodeInContainer(router, callee) and
        localRouter = getRouterNodeInContainer(router, getContainer())
      )
    }

    override Routing::Node getLastChild() { result = targetRouter }

    override predicate isInstalledAt(DataFlow::Node r, ControlFlowNode cfgNode) {
      r = localRouter and
      cfgNode = getEnclosingExpr()
    }
  }

  /**
   * A function that handles an incoming request.
   */
  class RouteHandler extends Node, DataFlow::FunctionNode {
    /**
     * Gets the `i`th parameter of this route handler.
     *
     * This is equivalent to `getParameter(i)` but returns a `RouteHandlerInput`.
     *
     * To find all references to this parameter, use `getInput(n).ref()`.
     */
    final RouteHandlerInput getInput(int n) { result = getParameter(n) }

    /**
     * Gets a parameter of this route handler.
     *
     * This is equivalent to `getAParameter()` but returns a `RouteHandlerInput`.
     *
     * To find all references to a parameter, use `getAnInput().ref()`.
     */
    final RouteHandlerInput getAnInput() { result = getAParameter() }

    /**
     * Gets a call that delegates the incoming request to the next route handler in the stack,
     * usually a call of the form `next()`.
     *
     * By default, any 0-argument invocation of one of the route handler's parameters
     * is considered a continuation invocation, since the other parameters (request and response)
     * will generally not be invoked as a function. Framework models may override this method
     * if the default behavior is inadequate for that framework.
     */
    DataFlow::CallNode getAContinuationInvocation() {
      result = getAnInput().ref().getAnInvocation() and
      result.getNumArgument() = 0
    }
  }

  /**
   * A parameter to a route handler function.
   */
  class RouteHandlerInput extends DataFlow::ParameterNode {
    RouteHandlerInput() { this = any(RouteHandler h).getAParameter() }

    /** Gets a data flow node referring to this route handler input. */
    private DataFlow::SourceNode ref(DataFlow::TypeTracker t) {
      t.start() and
      result = this
      or
      exists(DataFlow::TypeTracker t2 | result = ref(t2).track(t2, t))
    }

    /** Gets a data flow node referring to this route handler input. */
    DataFlow::SourceNode ref() { result = ref(DataFlow::TypeTracker::end()) }

    /**
     * Gets the corresponding route handler, that is, the function on which this is a parameter.
     */
    final RouteHandler getRouteHandler() { result.getAParameter() = this }

    /**
     * Gets a node that is stored in the given access path on this route handler input, either
     * during execution of this router handler, or in one of the preceding ones.
     */
    DataFlow::Node getValueFromAccessPath(string path) {
      exists(RouteHandler handler, int i, Node predecessor |
        this = handler.getParameter(i) and
        result = getAnAccessPathRhs(predecessor, i, path) and
        (handler.isGuardedBy(predecessor) or predecessor = handler)
      )
    }
  }

  /**
   * Gets a value that flows into the given access path of the `n`th route handler input at `base`.
   *
   * For example,
   * ```js
   * function handler(req, res, next) {
   *   res.locals.foo = 123;
   *   next();
   * }
   * ```
   * the node `123` flows into the `locals.foo` access path on the `res` parameter (`n=1`) of `handler`.
   *
   * Only route handlers that may invoke the continuation (`next()`) are considered, as the effect
   * is otherwise not observable by other route handlers.
   *
   * In addition to the above, also contains implicit assignments contributed by framework models,
   * based on `Node::Range::getValueAtAccessPath`.
   */
  private DataFlow::Node getAnAccessPathRhs(Node base, int n, string path) {
    // Assigned in the body of a route handler function, whi
    exists(RouteHandler handler | base = handler |
      result = AccessPath::getAnAssignmentTo(handler.getInput(n).ref(), path) and
      exists(handler.getAContinuationInvocation())
    )
    or
    // Implicit assignment contributed by framework model
    exists(DataFlow::Node value, string path1 |
      value = base.(Node::Range).getValueAtAccessPath(n, path1)
    |
      result = value and path = path1
      or
      exists(string path2 |
        result = AccessPath::getAnAssignmentTo(value.getALocalSource(), path2) and
        path = path1 + "." + path2
      )
    )
  }

  /**
   * Gets a value that refers to the given access path of the `n`th route handler input at `base`
   *
   * For example,
   * ```js
   * function handler2(req, res) {
   *   res.send(res.locals.foo);
   * }
   * ```
   * here the `res.locals.foo` expression refers to the `locals.foo` path on the `res` parameter (`n=1`)
   * of `handler2`.
   */
  private DataFlow::SourceNode getAnAccessPathRead(RouteHandler base, int n, string path) {
    result = AccessPath::getAReferenceTo(base.getInput(n).ref(), path) and
    not AccessPath::DominatingPaths::hasDominatingWrite(result)
  }

  /**
   * Like `getAnAccessPathRhs` but with `base` mapped to its root node.
   */
  private DataFlow::Node getAnAccessPathRhsUnderRoot(RootNode root, int n, string path) {
    result = getAnAccessPathRhs(root.getADescendant(), n, path)
  }

  /**
   * Like `getAnAccessPathRead` but with `base` mapped to its root node.
   */
  private DataFlow::SourceNode getAnAccessPathReadUnderRoot(RootNode root, int n, string path) {
    result = getAnAccessPathRead(root.getADescendant(), n, path)
  }

  /**
   * Holds if `pred -> succ` is an API-graph step between access paths on request input objects.
   * 
   * Since API graphs are mainly used to propagate type-like information, we do not require
   * a happens-before relation for this step. We only require that we stay within the same
   * web application, which is ensured by having a common root node.
   */
  private predicate middlewareApiStep(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
    exists(RootNode root, int n, string path |
      pred = getAnAccessPathRhsUnderRoot(root, n, path) and
      succ = getAnAccessPathReadUnderRoot(root, n, path)
    )
    or
    // We can't augment the call graph as this depends on type tracking, so just
    // manually add steps out of functions stored on a request input.
    exists(DataFlow::FunctionNode function, DataFlow::CallNode call |
      middlewareApiStep(function, call.getCalleeNode().getALocalSource()) and
      pred = function.getReturnNode() and
      succ = call
    )
  }

  /** Contributes `middlewareApiStep` as an API graph step. */
  private class MiddlewareApiStep extends API::AdditionalUseStep {
    override predicate step(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
      middlewareApiStep(pred, succ)
    }
  }

  /**
   * Holds if `pred -> succ` is a data-flow step between access paths on request input objects.
   */
  private predicate middlewareDataFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Node writer, Node reader, int n, string path |
      pred = getAnAccessPathRhs(writer, n, path) and
      succ = getAnAccessPathRead(reader, n, path) and
      reader.isGuardedBy(writer)
    )
    or
    // Same as in `apiStep`: we can't augment the call graph, so just add flow out
    // of functions stored on a request input.
    exists(DataFlow::FunctionNode function, DataFlow::CallNode call |
      middlewareDataFlowStep(function.getALocalUse(), call.getCalleeNode().getALocalSource()) and
      pred = function.getReturnNode() and
      succ = call
    )
  }

  /** Contributes `middlewareDataFlowStep` as a value-preserving data flow step. */
  private class MiddlewareFlowStep extends DataFlow::SharedFlowStep {
    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      middlewareDataFlowStep(pred, succ)
    }
  }
}
