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
      /** Gets a node that flows to this use site. */
      DataFlow::Node getSource() {
        result = getALocalSource()
        or
        StepSummary::smallstep(result, this, routeStepSummary())
        or
        HTTP::routeHandlerStep(result, this)
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
      abstract predicate isInstalledAt(DataFlow::SourceNode router, ControlFlowNode cfgNode);
    }

    /**
     * A route setup that is method call on a router object, installing its arguments as route handlers.
     *
     * This class can be extended to contribute new kinds of route handlers.
     */
    abstract class MethodCall extends RouteSetup::Range, Node::WithArguments,
      DataFlow::MethodCallNode {
      override DataFlow::Node getChild(int n) { result = getArgument(n) }

      override predicate isInstalledAt(DataFlow::SourceNode router, ControlFlowNode cfgNode) {
        router = getReceiver().getALocalSource() and cfgNode = getEnclosingExpr()
      }
    }
  }

  /**
   * A `Node` generated from the router targeted by a `RouteSetup`.
   */
  private class RouterRange extends Node::Range, DataFlow::SourceNode {
    RouterRange() { any(RouteSetup::Range setup).isInstalledAt(this, _) }

    override Node getLastChild() {
      // TODO: handle mutation through captured reference
      result = getMostRecentRouteSetupAt(this, getContainer().getExit())
    }

    override predicate hasSiblingChildren(Node pred, Node succ) {
      exists(ControlFlowNode cfgNode |
        succ.(RouteSetup::Range).isInstalledAt(this, cfgNode) and
        pred = getMostRecentRouteSetupAt(this, cfgNode.getAPredecessor())
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
    result.isInstalledAt(router, node)
    or
    result = getMostRecentRouteSetupAt(router, node.getAPredecessor()) and
    not exists(RouteSetup::Range setup | setup.isInstalledAt(router, node))
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
      DataFlow::argumentPassingStep(this, localRouter, _, targetRouter)
      or
      FlowSteps::returnStep(targetRouter, this) and
      localRouter = this
    }

    override Routing::Node getLastChild() { result = targetRouter }

    override predicate isInstalledAt(DataFlow::SourceNode r, ControlFlowNode cfgNode) {
      r = localRouter.getALocalSource() and
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

  pragma[nomagic]
  private predicate relevantAccessPath(string path) {
    exists(getAnAccessPathRhs(_, _, path)) and
    exists(getAnAccessPathRead(_, _, path))
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
   * An API-graph step between access paths on request input objects.
   * 
   * Since API graphs are mainly used to propagate type-like information, we do not require
   * a happens-before relation for this step. We only require that we stay within the same
   * web application, which is ensured by having a common root node.
   */
  private class MiddlewareApiStep extends API::AdditionalUseStep {
    override predicate step(DataFlow::SourceNode pred, DataFlow::SourceNode succ) {
      exists(RootNode root, int n, string path |
        pred = getAnAccessPathRhsUnderRoot(root, n, path) and
        succ = getAnAccessPathReadUnderRoot(root, n, path)
      )
    }
  }

  /**
   * A data-flow step between access paths on request input objects.
   */
  private class MiddlewareFlowStep extends DataFlow::SharedFlowStep {
    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      // TODO: require happens-before, but for now just check if they're in the same app
      exists(RootNode root, int n, string path |
        pred = getAnAccessPathRhsUnderRoot(root, n, path) and
        succ = getAnAccessPathReadUnderRoot(root, n, path)
      )
    }
  }
}
