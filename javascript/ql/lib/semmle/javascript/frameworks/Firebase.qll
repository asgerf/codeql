/**
 * Provides classes and predicates for reasoning about code using the Firebase API.
 */

import javascript

module Firebase {
  /** Gets a reference to the Firebase API object. */
  private DataFlow::SourceNode firebase() {
    result = DataFlow::moduleImport("firebase/app")
    or
    result = DataFlow::moduleImport("firebase-admin")
    or
    result = DataFlow::globalVarRef("firebase")
  }

  /** Gets a reference to a Firebase app created with `initializeApp`. */
  private DataFlow::SourceNode initApp() {
    result = firebase().getAGlobalMethodCall("initializeApp")
    or
    result.hasUnderlyingType("firebase", "app.App")
  }

  /**
   * Gets a reference to a Firebase app, either the `firebase` object or an
   * app created explicitly with `initializeApp()`.
   */
  DataFlow::SourceNode app() { result = [firebase(), initApp()] }

  module Database {
    /** Gets a reference to a Firebase database object, such as `firebase.database()`. */
    DataFlow::SourceNode database() {
      result = app().getAGlobalMethodCall("database")
      or
      result.hasUnderlyingType("firebase", "database.Database")
    }

    /** Gets a node that refers to a `Reference` object, such as `firebase.database().ref()`. */
    DataFlow::SourceNode ref() {
      exists(string name | result = database().getAGlobalMethodCall(name) |
        name = "ref" or
        name = "refFromURL"
      )
      or
      exists(string name | result = ref().getAGlobalMethodCall(name) |
        name = "push" or
        name = "child"
      )
      or
      exists(string name | result = ref().getAGlobalPropertyRead(name) |
        name = "parent" or
        name = "root"
      )
      or
      result = snapshot().getAGlobalPropertyRead("ref")
      or
      result.hasUnderlyingType("firebase", "database.Reference")
    }

    /** Gets a node that refers to a `Query` or `Reference` object. */
    DataFlow::SourceNode query() {
      result = ref() // a Reference can be used as a Query
      or
      exists(string name | result = query().getAGlobalMethodCall(name) |
        name = "endAt" or
        name = "limitTo" + any(string s) or
        name = "orderBy" + any(string s) or
        name = "startAt"
      )
      or
      result.hasUnderlyingType("firebase", "database.Query")
    }

    /**
     * A call of form `query.on(...)` or `query.once(...)`.
     */
    class QueryListenCall extends DataFlow::MethodCallNode {
      QueryListenCall() {
        this = query().getAGlobalMethodCall() and
        (this.getMethodName() = "on" or this.getMethodName() = "once")
      }

      /**
       * Gets the argument in which the callback is passed.
       */
      DataFlow::Node getCallbackNode() { result = this.getArgument(1) }
    }

    /**
     * Gets a node that is passed as the callback to a `Reference.transaction` call.
     */
    DataFlow::SourceNode transactionCallback() {
      result =
        ref().getAGlobalMethodCall("transaction").getArgument(0).getALocalSource().backtrack()
    }
  }

  /**
   * Provides predicates for reasoning about the the Firebase Cloud Functions API,
   * sometimes referred to just as just "Firebase Functions".
   */
  module CloudFunctions {
    /** Gets a reference to the Cloud Functions namespace. */
    DataFlow::SourceNode namespace() { result = DataFlow::moduleImport("firebase-functions") }

    /** Gets a reference to a Cloud Functions database object. */
    DataFlow::SourceNode database() { result = namespace().getAGlobalPropertyRead("database") }

    /** Gets a data flow node holding a `RefBuilder` object. */
    DataFlow::SourceNode refBuilder() { result = database().getAGlobalMethodCall("ref") }

    /** A call that registers a listener on a `RefBuilder`, such as `ref.onCreate(...)`. */
    class RefBuilderListenCall extends DataFlow::MethodCallNode {
      RefBuilderListenCall() {
        this = refBuilder().getAGlobalMethodCall() and
        this.getMethodName() = "on" + any(string s)
      }

      /**
       * Gets the data flow node holding the listener callback.
       */
      DataFlow::Node getCallbackNode() { result = this.getArgument(0) }
    }

    /**
     * A call to a Firebase method that sets up a route.
     */
    private class RouteSetup extends Http::Servers::StandardRouteSetup, DataFlow::CallNode {
      RouteSetup() {
        this = namespace().getAGlobalPropertyRead("https").getAGlobalMemberCall("onRequest")
      }

      override DataFlow::SourceNode getARouteHandler() {
        result = this.getArgument(0).getALocalSource().backtrack()
      }

      override DataFlow::Node getServer() { none() }
    }

    /**
     * A function used as a route handler.
     */
    private class RouteHandler extends Express::RouteHandler, Http::Servers::StandardRouteHandler,
      DataFlow::FunctionNode
    {
      RouteHandler() { this = any(RouteSetup setup).getARouteHandler() }

      override DataFlow::ParameterNode getRouteHandlerParameter(string kind) {
        kind = "request" and result = this.getParameter(0)
        or
        kind = "response" and result = this.getParameter(1)
      }
    }
  }

  /**
   * Gets a value that will be invoked with a `DataSnapshot` value as its first parameter.
   */
  DataFlow::SourceNode snapshotCallback() {
    result = any(Database::QueryListenCall call).getCallbackNode().getALocalSource().backtrack()
    or
    result =
      any(CloudFunctions::RefBuilderListenCall call).getCallbackNode().getALocalSource().backtrack()
  }

  /**
   * Gets a node that refers to a `DataSnapshot` value, such as `x` in
   * `firebase.database().ref().on('value', x => {...})`.
   */
  DataFlow::SourceNode snapshot() {
    result = snapshotCallback().(DataFlow::FunctionNode).getParameter(0)
    or
    result instanceof Database::QueryListenCall // returns promise
    or
    result = snapshot().getAGlobalMethodCall("child")
    or
    result = snapshot().getAGlobalMethodCall("forEach").getCallback(0).getParameter(0)
    or
    exists(string prop | result = snapshot().getAGlobalPropertyRead(prop) |
      prop = "before" or // only defined on Change objects
      prop = "after"
    )
    or
    result.hasUnderlyingType("firebase", "database.DataSnapshot")
    or
    TaintTracking::promiseStep(snapshot().track(), result)
  }

  /**
   * A reference to a value obtained from a Firebase database.
   */
  class FirebaseVal extends RemoteFlowSource {
    FirebaseVal() {
      exists(string name | this = snapshot().getAGlobalMethodCall(name) |
        name = "val" or
        name = "exportVal"
      )
      or
      this = Database::transactionCallback().(DataFlow::FunctionNode).getParameter(0)
    }

    override string getSourceType() { result = "Firebase database" }
  }
}
