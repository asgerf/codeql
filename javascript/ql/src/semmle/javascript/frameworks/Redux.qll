/**
 * Provides classes and predicates for reasoning about data flow through the redux package.
 */

import javascript

// The core Redux model contributes two kinds of steps:
//   1. From dispatch argument to reducer parameter ("dispatch step")
//   2. From reducer return-value to state access ("reducer step")
//
// A third kind of step is also needed to adapter libraries like `react-redux`, for example:
//   3. From mapStateToProps return-value to props access in react component
//
// The third kind of step is technically independent of the core Redux library, but
// this file includes modeling of such adapter libraries as well.
//
// The first step, from dispatch to reducer, has to deal with type tags, so it can't always
// map to a function parameter.

// TODO: typescript-fsa family of packages
// TODO: handle immer-style `state.foo = foo` assignments in reducer; add steps back to state access paths

module Redux {
  private class ReduxRootStateTag extends DataFlow::CustomNodes::SingletonNodeTag {
    ReduxRootStateTag() { this = "redux-root-state" }
  }

  private class ReduxRootStateNode extends DataFlow::CustomNodes::SingletonNode,
    DataFlow::SourceNode::Range {
    override ReduxRootStateTag tag;
  }

  private ReduxRootStateNode rootState() { any() }

  /** An API node referring to the root state. */
  abstract private class RootStateNode extends API::Node { }

  /** Gets an API node corresponding to an access of `prop` on the root state. */
  pragma[noinline]
  private API::Node rootStateProp(string prop) { result = any(RootStateNode n).getMember(prop) }

  /**
   * Gets a node interprocedurally reachable from `source`, where `source` must be known
   * to have a corresponding use-node in the API graph.
   *
   * We use this to maintain a consistent interface based on data-flow nodes, while being
   * able to reuse the type-tracking done by API graphs in cases where the node is known to
   * be part of the API graph.
   */
  pragma[inline]
  private DataFlow::SourceNode getAnApiReference(DataFlow::SourceNode source) {
    exists(API::Node apiNode |
      apiNode.getAnImmediateUse() = source and
      result = apiNode.getAUse()
    )
  }

  class StoreCreation extends DataFlow::SourceNode {
    StoreCreation::Range range;

    StoreCreation() { this = range }

    /** Gets a reference to the store. */
    DataFlow::SourceNode ref() { result = getAnApiReference(this) }

    /** Gets the data flow node holding the root reducer for this store. */
    DataFlow::Node getReducerArg() { result = range.getReducerArg() }

    /** Gets a data flow node referring to the root reducer. */
    DataFlow::SourceNode getAReducerSource() { result = getReducerArg().(ReducerArg).getASource() }
  }

  module StoreCreation {
    abstract class Range extends DataFlow::SourceNode {
      abstract DataFlow::Node getReducerArg();
    }

    private class CreateStore extends DataFlow::CallNode, Range {
      CreateStore() { this = API::moduleImport(["redux", "@reduxjs/toolkit"]).getMember("createStore").getACall() }

      override DataFlow::Node getReducerArg() { result = getArgument(0) }
    }

    private class ToolkitStore extends API::CallNode, Range {
      ToolkitStore() {
        this = API::moduleImport("@reduxjs/toolkit").getMember("configureStore").getACall()
      }

      override DataFlow::Node getReducerArg() {
        result = getParameter(0).getMember("reducer").getARhs()
      }
    }
  }

  /** A data flow node that is used as a reducer. */
  private class ReducerArg extends DataFlow::Node {
    ReducerArg() {
      this = any(StoreCreation c).getReducerArg()
      or
      this = any(DelegatingReducer r).getStateHandlerArg(_)
      or
      this = any(DelegatingReducer r).getActionHandlerArg(_)
    }

    /** Gets a data flow node that flows to this reducer argument. */
    DataFlow::SourceNode getASource(DataFlow::TypeBackTracker t) {
      t.start() and
      result = getALocalSource()
      or
      exists(DataFlow::Node mid | result.flowsTo(mid) |
        // Step through forwarding functions
        DataFlow::functionForwardingStep(mid, getASource(t.continue()))
        or
        // Step through library functions like `redux-persist`
        mid = getASource(t.continue()).(DelegatingReducer).getAPlainHandlerArg()
        or
        // Step through function composition (usually composed with various state "enhancer" functions)
        exists(FunctionCompositionCall compose, DataFlow::CallNode call |
          call = compose.getACall() and
          getASource(t.continue()) = call and
          mid = [compose.getAnOperandNode(), call.getAnArgument()]
        )
      )
      or
      exists(DataFlow::TypeBackTracker t2 | result = getASource(t2).backtrack(t2, t))
    }

    /** Gets a data flow node that flows to this reducer argument. */
    DataFlow::SourceNode getASource() { result = getASource(DataFlow::TypeBackTracker::end()) }

    /**
     * Holds if the actions discpatched to thsi reducer have the given type, that is,
     * it is created by an action creator that flows to `actionType`, or has `action.type` set to
     * the string value of `actionType`.
     */
    predicate isActionTypeHandler(DataFlow::Node actionType) {
      exists(DelegatingReducer r |
        this = r.getActionHandlerArg(actionType)
        or
        this = r.getStateHandlerArg(_) and
        r.getUseSite().isActionTypeHandler(actionType)
      )
    }

    /**
     * Holds if the actions dispatched to this reducer have the given `action.type` value.
     */
    predicate isTypeTagHandler(string actionType) {
      exists(DataFlow::Node node |
        isActionTypeHandler(node) and
        actionType = getATypeTagFromNode(node)
      )
    }

    /**
     * Holds if this reducer operates on the root state, as opposed to some access path within the state.
     */
    predicate isRootStateHandler() {
      this = any(StoreCreation c).getReducerArg()
      or
      exists(DelegatingReducer r |
        this = r.getActionHandlerArg(_) and
        r.getUseSite().isRootStateHandler()
      )
    }

    /**
     * Gets an API node for a state access to which the return value of this reducer should flow into.
     *
     * Has no result for root state accesses; those are special-cased in `getAffectedStateNode`.
     */
    private API::Node getAnAffectedStateApiNode() {
      exists(DelegatingReducer r |
        this = r.getActionHandlerArg(_) and
        result = r.getUseSite().getAnAffectedStateApiNode()
        or
        exists(DataFlow::Node succ |
          ReactRedux::stateToPropsStep(getAnAffectedStateApiNode().getAUse(), succ) and
          result.getAnImmediateUse() = succ
        )
        or
        exists(string prop | this = r.getStateHandlerArg(prop) |
          result = r.getUseSite().getAnAffectedStateApiNode().getMember(prop)
          or
          r.getUseSite().isRootStateHandler() and
          result = rootStateProp(prop)
        )
      )
    }

    /**
     * Gets a state access affected by the return value of this reducer.
     */
    DataFlow::SourceNode getAnAffectedStateNode() {
      result = getAnAffectedStateApiNode().getAnImmediateUse()
      or
      isRootStateHandler() and
      result = rootState()
    }
  }

  abstract class DelegatingReducer extends DataFlow::SourceNode {
    DataFlow::Node getStateHandlerArg(string prop) { none() }

    /**
     * Gets a data flow node holding a reducer to which this one forwards its arguments when
     * the dispatched action is of the given type.
     *
     * `actionType` may refer to a string value corresponding to `action.type`, or an action creator, if
     * this reducer handles actions created by that.
     */
    DataFlow::Node getActionHandlerArg(DataFlow::Node actionType) { none() }

    /**
     * Gets a data flow node holding a reducer to which this one forwards every (state, action) pair
     * (for the purposes of this model).
     */
    DataFlow::Node getAPlainHandlerArg() { none() }

    /** Gets the use site of this reducer. */
    final ReducerArg getUseSite() { result.getASource() = this }
  }

  private API::Node combineReducers() {
    result = API::moduleImport(["redux", "redux-immutable", "@reduxjs/toolkit"]).getMember("combineReducers")
  }

  /**
   * A call to `combineReducers`, which delegates properties of `state` to individual sub-reducers.
   */
  private class CombineReducers extends API::CallNode, DelegatingReducer {
    CombineReducers() {
      this = combineReducers().getACall()
    }

    override DataFlow::Node getStateHandlerArg(string prop) {
      result = getParameter(0).getMember(prop).getARhs()
    }
  }

  /**
   * An object literal flowing into a nested property in a `combineReducers` object, such as the `{ bar }` object in:
   * ```js
   * combineReducers({ foo: { bar } })
   * ```
   *
   * Although the object itself is clearly not a function, we use the object to model the corresponding reducer function created by `combineReducers`.
   */
  private class NestedCombineReducers extends DelegatingReducer, DataFlow::ObjectLiteralNode {
    NestedCombineReducers() {
      this = combineReducers().getParameter(0).getAMember+().getAValueReachingRhs()
    }

    override DataFlow::Node getStateHandlerArg(string prop) {
      result = getAPropertyWrite(prop).getRhs()
    }
  }

  /** Gets the `redux-actions` library or one similar enough that we can model them as identical. */
  private API::Node reduxActionsLike() {
    result = API::moduleImport(["redux-actions", "redux-ts-utils"])
  }

  /**
   * Gets the type tag of an action creator reaching `node`, or the type tag from one of the action
   * types passed to a `combineActions` call reaching `node`.
   */
  private string getAnActionTypeTag(DataFlow::SourceNode node) {
    exists(ActionCreator action |
      node = action.ref() and
      result = action.getTypeTag()
    )
    or
    exists(API::CallNode combiner |
      combiner = reduxActionsLike().getMember("combineActions").getACall() and
      node = combiner.getReturn().getAUse() and
      (
        combiner.getAnArgument().mayHaveStringValue(result)
        or
        result = getAnActionTypeTag(combiner.getAnArgument().getALocalSource())
      )
    )
  }

  /** Gets the type tag of an action reaching `node`, or the string value of `node`. */
  pragma[inline] // Inlined to avoid duplicating `mayHaveStringValue`
  private string getATypeTagFromNode(DataFlow::Node node) {
    node.mayHaveStringValue(result)
    or
    result = getAnActionTypeTag(node.getALocalSource())
  }

  private class HandleActions extends API::CallNode, DelegatingReducer {
    HandleActions() {
      this = reduxActionsLike().getMember("handleActions").getACall()
    }

    override DataFlow::Node getActionHandlerArg(DataFlow::Node actionType) {
      exists(DataFlow::PropWrite write |
        result = getParameter(0).getAMember().getARhs() and
        write.getRhs() = result and
        actionType = write.getPropertyNameExpr().flow()
      )
    }
  }

  private class HandleAction extends API::CallNode, DelegatingReducer {
    HandleAction() {
      this = reduxActionsLike().getMember("handleAction").getACall()
    }

    override DataFlow::Node getActionHandlerArg(DataFlow::Node actionType) {
      actionType = getArgument(0) and
      result = getArgument(1)
    }
  }

  private class PersistReducer extends DataFlow::CallNode, DelegatingReducer {
    PersistReducer() {
      this = API::moduleImport("redux-persist").getMember("persistReducer").getACall()
    }

    override DataFlow::Node getAPlainHandlerArg() {
      result = getArgument(1)
    }
  }

  private class ImmerProduce extends DataFlow::CallNode, DelegatingReducer {
    ImmerProduce() {
      this = API::moduleImport("immer").getACall()
      or
      this = API::moduleImport("immer").getMember("produce").getACall()
    }

    override DataFlow::Node getAPlainHandlerArg() {
      result = getArgument(0)
    }
  }

  /**
   * Model `reduce-reducers` as a reducer that dispatches to an arbitrary subreducer.
   *
   * Concretely, it chains together all of the reducers, but in practice it is only used
   * when the reducers handle a disjoint set of action types.
   */
  private class ReduceReducers extends DataFlow::CallNode, DelegatingReducer {
    ReduceReducers() {
      this = API::moduleImport("reduce-reducers").getACall() or
      this = reduxActionsLike().getMember("reduceReducers").getACall()
    }

    override DataFlow::Node getAPlainHandlerArg() {
      result = getAnArgument()
      or
      result = getArgument(0).getALocalSource().(DataFlow::ArrayCreationNode).getAnElement()
    }
  }

  private class CreateReducer extends API::CallNode, DelegatingReducer {
    CreateReducer() {
      this = API::moduleImport("@reduxjs/toolkit").getMember("createReducer").getACall()
    }

    private API::Node getABuilderRef() {
      result = getParameter(1).getParameter(0)
      or
      result = getABuilderRef().getAMember().getReturn()
    }

    override DataFlow::Node getActionHandlerArg(DataFlow::Node actionType) {
      exists(API::CallNode addCase |
        addCase = getABuilderRef().getMember("addCase").getACall() and
        actionType = addCase.getArgument(0) and
        result = addCase.getArgument(1)
      )
    }
  }

  private class CreateSliceReducer extends DelegatingReducer {
    API::CallNode call;

    CreateSliceReducer() {
      call = API::moduleImport("@reduxjs/toolkit").getMember("createSlice").getACall() and
      this = call.getReturn().getMember("reducer").getAnImmediateUse()
    }

    private API::Node getABuilderRef() {
      result = call.getParameter(0).getMember("extraReducers").getParameter(0)
      or
      result = getABuilderRef().getAMember().getReturn()
    }

    override DataFlow::Node getActionHandlerArg(DataFlow::Node actionType) {
      exists(string name |
        result = call.getParameter(0).getMember("reducers").getMember(name).getARhs() and
        actionType = call.getReturn().getMember("actions").getMember(name).getAnImmediateUse()
      )
      or
      // Properties of 'extraReducers':
      //   { extraReducers: { [action]: reducer }}
      exists(DataFlow::PropWrite write |
        result = call.getParameter(0).getMember("extraReducers").getAMember().getARhs() and
        write.getRhs() = result and
        actionType = write.getPropertyNameExpr().flow()
      )
      or
      // Builder callback to 'extraReducers':
      //   extraReducers: builder => builder.addCase(action, reducer)
      exists(API::CallNode addCase |
        addCase = getABuilderRef().getMember("addCase").getACall() and
        actionType = addCase.getArgument(0) and
        result = addCase.getArgument(1)
      )
    }
  }

  private class CreateSliceAction extends ActionCreator::Range {
    API::CallNode call;
    string actionName;

    CreateSliceAction() {
      call = API::moduleImport("@reduxjs/toolkit").getMember("createSlice").getACall() and
      this = call.getReturn().getMember("actions").getMember(actionName).getAnImmediateUse()
    }

    override string getTypeTag() {
      exists(string prefix |
        call.getParameter(0).getMember("name").getARhs().mayHaveStringValue(prefix) and
        result = prefix + "/" + actionName
      )
    }
  }

  /**
   * A source of the `dispatch` function, used as starting point for `getADispatchFunctionReference`.
   */
  abstract private class DispatchFunctionSource extends DataFlow::SourceNode { }

  /**
   * A value that is dispatched, that is, flows to the first argument of `dispatch`
   * (but where the call to `dispatch` is not necessarily explicit in the code).
   *
   * Used as starting point for `getADispatchedValueSource`.
   */
  abstract private class DispatchedValueSink extends DataFlow::Node { }

  private class StoreDispatchSource extends DispatchFunctionSource {
    StoreDispatchSource() { this = any(StoreCreation c).ref().getAPropertyRead("dispatch") }
  }

  /** Gets a data flow node referring to the `dispatch` function. */
  private DataFlow::SourceNode getADispatchFunctionReference(DataFlow::TypeTracker t) {
    t.start() and
    result instanceof DispatchFunctionSource
    or
    // When using the redux-thunk middleware, dispatching a function value results in that
    // function being invoked with (dispatch, getState).
    // We simply assume redux-thunk middleware is always installed.
    t.start() and
    result = getADispatchedValueSource().(DataFlow::FunctionNode).getParameter(0)
    or
    exists(DataFlow::TypeTracker t2 | result = getADispatchFunctionReference(t2).track(t2, t))
  }

  /** Gets a data flow node referring to the `dispatch` function. */
  DataFlow::SourceNode getADispatchFunctionReference() {
    result = getADispatchFunctionReference(DataFlow::TypeTracker::end())
  }

  /** Gets a data flow node that is dispatched as an action. */
  private DataFlow::SourceNode getADispatchedValueSource(DataFlow::TypeBackTracker t) {
    t.start() and
    result = any(DispatchedValueSink d).getALocalSource()
    or
    t.start() and
    result = getADispatchFunctionReference().getACall().getArgument(0).getALocalSource()
    or
    exists(DataFlow::TypeBackTracker t2 | result = getADispatchedValueSource(t2).backtrack(t2, t))
  }

  /**
   * Gets a data flow node that is dispatched as an action, that is, it flows to the first argument of `dispatch`.
   */
  DataFlow::SourceNode getADispatchedValueSource() {
    result = getADispatchedValueSource(DataFlow::TypeBackTracker::end())
  }

  /** Gets the `action` parameter of a reducer that isn't behind an implied type guard. */
  DataFlow::SourceNode getAnUntypedActionInReducer() {
    exists(ReducerArg reducer |
      not reducer.isTypeTagHandler(_) and
      result = reducer.getASource().(DataFlow::FunctionNode).getParameter(1)
    )
  }

  /** A call to `bindActionCreators` */
  private class BindActionCreatorsCall extends API::CallNode {
    BindActionCreatorsCall() {
      this = API::moduleImport(["redux", "@reduxjs/toolkit"]).getMember("bindActionCreators").getACall()
    }
  }

  /** The return value of a function flowing into `bindActionCreators` is dispatched */
  private class BindActionDispatchSink extends DispatchedValueSink {
    BindActionDispatchSink() {
      this = any(BindActionCreatorsCall c).getParameter(0).getAMember().getReturn().getARhs()
    }
  }

  /**
   * A function value, which, for some string `T` behaves as the function `x => {type: T, payload: x}`.
   */
  class ActionCreator extends DataFlow::SourceNode {
    ActionCreator::Range range;
  
    ActionCreator() { this = range }

    string getTypeTag() { result = range.getTypeTag() }

    DataFlow::FunctionNode getMiddlewareFunction() { result = range.getMiddlewareFunction() }

    /** Gets a data flow node referring to this action creator. */
    private DataFlow::SourceNode ref(DataFlow::TypeTracker t) {
      t.start() and
      result = this 
      or
      exists(BindActionCreatorsCall bind, string prop |
        ref(t.continue()).flowsTo(bind.getParameter(0).getMember(prop).getARhs()) and
        result = bind.getReturn().getMember(prop).getAnImmediateUse()
      ) // TODO: step through mapDispatchToProps etc
      or
      ReactRedux::dispatchToPropsStep(ref(t.continue()).getALocalUse(), result)
      or
      exists(DataFlow::TypeTracker t2 |
        result = ref(t2).track(t2, t)
      )
    }
    
    /** Gets a data flow node referring to this action creator. */
    DataFlow::SourceNode ref() {
      result = ref(DataFlow::TypeTracker::end())
    }
  
    /**
     * Gets a node that evaluates to `outcome` if `action` is an action created by this action creator.
     */
    DataFlow::Node getATypeTest(DataFlow::Node action, boolean outcome) {
      // TODO: handle switch (maybe via MembershipCandidate)
      exists(DataFlow::CallNode call |
        call = ref().getAMethodCall("match") and
        action = call.getArgument(0) and
        outcome = true and
        result = call
      )
      or
      exists(DataFlow::SourceNode actionSrc, EqualityTest test |
        actionSrc = getAnUntypedActionInReducer() and
        actionSrc.flowsTo(action) and
        test.hasOperands(actionSrc.getAPropertyRead("type").asExpr(), any(Expr e | e.mayHaveStringValue(getTypeTag()))) and
        outcome = test.getPolarity() and
        result = test.flow()
      )
    }

    /**
     * Holds if `successBlock`  when a check has determined that `action` originated from this action creator.
     */
    private ReachableBasicBlock getASuccessfulTypeCheckBlock( DataFlow::SourceNode action) {
      result = getASuccessfulTypeCheckBlock(action, getTypeTag())
      or
      exists(ConditionGuardNode guard, DataFlow::CallNode call |
        call = ref().getAMethodCall("match") and
        guard.getTest() = call.asExpr() and
        action.flowsTo(call.getArgument(0)) and
        guard.getOutcome() = true and
        result = guard.getBasicBlock()
      )
    }

    /** Gets a data flow node referring a payload of this action (usually in the reducer function). */
    DataFlow::SourceNode getAPayloadReference() {
      // `if (x.match(action)) { ... action.payload ... }`
      exists(DataFlow::SourceNode actionSrc |
        result = actionSrc.getAPropertyRead("payload") and
        getASuccessfulTypeCheckBlock(actionSrc).dominates(result.getBasicBlock())
      )
      or
      exists(ReducerArg reducer |
        (
          reducer.isTypeTagHandler(getTypeTag())
          or
          reducer.isActionTypeHandler(ref().getALocalUse())
        ) and
        result = reducer.getASource().(DataFlow::FunctionNode).getParameter(1).getAPropertyRead("payload")
      )
    }
  }

  module ActionCreator {
    abstract class Range extends DataFlow::SourceNode {
      abstract string getTypeTag();
      DataFlow::FunctionNode getMiddlewareFunction() { none() }
      DataFlow::Node getAnAdditionalTypeTest(DataFlow::Node action, boolean outcome) { none() }
    }

    class SingleAction extends Range, API::CallNode {
      SingleAction() {
        this =
          API::moduleImport(["@reduxjs/toolkit", "redux-actions", "redux-ts-utils"])
              .getMember("createAction")
              .getACall()
      }

      override string getTypeTag() {
        getArgument(0).mayHaveStringValue(result)
      }
    }

    /** One of the dispatchers created by a call to `createActions` from `redux-actions`. */
    class MultiAction extends Range {
      API::CallNode createActions;
      string name;

      MultiAction() {
        createActions = API::moduleImport("redux-actions").getMember("createActions").getACall() and
        this = createActions.getReturn().getMember(name).getAnImmediateUse()
      }

      override DataFlow::FunctionNode getMiddlewareFunction() {
        result.flowsTo(createActions.getParameter(0).getMember(getTypeTag()).getARhs())
      }

      override string getTypeTag() {
        result = name.regexpReplaceAll("([a-z])([A-Z])", "$1_$2").toUpperCase()
      }
    }
  }

  /**
   * Holds if `pred -> succ` is step an action to its use in a reducer function.
   */
  predicate actionToReducerStep(DataFlow::Node pred, DataFlow::SourceNode succ) {
    // Actions created by an action creator library
    exists(ActionCreator action |
      exists(DataFlow::CallNode call | call = action.ref().getACall() |
        exists(int i |
          pred = call.getArgument(i) and
          succ = action.getMiddlewareFunction().getParameter(i)
        )
        or
        not exists(action.getMiddlewareFunction()) and
        pred = call.getArgument(0) and
        succ = action.getAPayloadReference()
      )
      or
      pred = action.getMiddlewareFunction().getReturnNode() and
      succ = action.getAPayloadReference()
    )
    or
    // Manually created and dispatched actions
    exists(string actionType, string prop, DataFlow::SourceNode actionSrc |
      pred = getAManuallyDispatchedValue(actionType).getAPropertyWrite(prop).getRhs() and
      succ = actionSrc.getAPropertyRead(prop)
    |
      getASuccessfulTypeCheckBlock(actionSrc, actionType).dominates(succ.getBasicBlock())
      or
      exists(ReducerArg reducer |
        reducer.isTypeTagHandler(actionType) and
        actionSrc = reducer.getASource().(DataFlow::FunctionNode).getParameter(1)
      )
    )
  }

  private class ActionToReducerStep extends DataFlow::AdditionalFlowStep {
    ActionToReducerStep() {
      actionToReducerStep(_, this)
    }

    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      actionToReducerStep(pred, succ) and succ = this
    }
  }

  /**
   * Holds if `pred -> succ` is a step from the return value of a reducer function to
   * a corresponding state access.
   */
  predicate reducerToStateStep(DataFlow::Node pred, DataFlow::SourceNode succ) {
    exists(ReducerArg arg, DataFlow::FunctionNode function |
      function = arg.getASource() and
      pred = function.getReturnNode() and
      succ = arg.getAnAffectedStateNode()
    )
    or
    // To avoid a cartesian product between all root state reducers and all root state accesses,
    // we use a synthetic singleton node as a junction between these. All reducers flow to the synthetic node,
    // and the synthetic node flows to all uses.
    pred = rootState() and
    succ = any(RootStateNode n).getAUse()
  }

  private class ReducerToStateStep extends DataFlow::AdditionalFlowStep {
    ReducerToStateStep() {
      reducerToStateStep(_, this)
    }

    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      reducerToStateStep(pred, succ) and succ = this
    }
  }

  /**
   * Gets a dispatched object literal with a property `type: actionType`.
   */
  private DataFlow::ObjectLiteralNode getAManuallyDispatchedValue(string actionType) {
    result.getAPropertyWrite("type").getRhs().mayHaveStringValue(actionType) and
    result = getADispatchedValueSource()
  }

  /**
   * Gets the block to be executed after a check has determined that `action.type` is `actionType`.
   */
  private ReachableBasicBlock getASuccessfulTypeCheckBlock(DataFlow::SourceNode action, string actionType) {
    action = getAnUntypedActionInReducer() and
    (
      exists(MembershipCandidate candidate, ConditionGuardNode guard |
        action.getAPropertyRead("type").flowsTo(candidate) and
        candidate.getAMemberString() = actionType and
        guard.getTest() = candidate.getTest().asExpr() and
        guard.getOutcome() = candidate.getTestPolarity() and
        result = guard.getBasicBlock()
      )
      or
      exists(SwitchStmt switch, SwitchCase case |
        action.getAPropertyRead("type").flowsTo(switch.getExpr().flow()) and
        case = switch.getACase() and
        case.getExpr().mayHaveStringValue(actionType) and
        result = getCaseBlock(case)
      )
    )
  }

  /** Gets the block to execute with `case` matches sucessfully. */
  private BasicBlock getCaseBlock(SwitchCase case) {
    result = case.getBodyStmt(0).getBasicBlock()
    or
    not exists(case.getABodyStmt()) and
    exists(SwitchStmt stmt, int i |
      stmt.getCase(i) = case and
      result = getCaseBlock(stmt.getCase(i + 1))
    )
  }

  private module ReactRedux {
    API::Node useSelector() { result = API::moduleImport("react-redux").getMember("useSelector") }

    /**
     * Step out of a `useSelector` call, such as from `state.x` to the result of `useSelector(state => state.x)`.
     */
    class UseSelectorStep extends API::CallNode, DataFlow::AdditionalFlowStep {
      UseSelectorStep() { this = useSelector().getACall() }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        pred = getParameter(0).getReturn().getARhs() and
        succ = this
      }
    }

    /** The argument to a `useSelector` callback, seen as a root state reference. */
    class UseSelectorStateSource extends RootStateNode {
      UseSelectorStateSource() { this = useSelector().getParameter(0).getParameter(0) }
    }

    /** A call to `useDispatch`, as a source of the `dispatch` function. */
    private class UseDispatchFunctionSource extends DispatchFunctionSource {
      UseDispatchFunctionSource() {
        this = API::moduleImport("react-redux").getMember("useDispatch").getReturn().getAnImmediateUse()
      }
    }

    private class RealConnectFunction extends ConnectCall {
      RealConnectFunction() {
        this = API::moduleImport("react-redux").getMember("connect").getACall()
      }

      override API::Node getMapStateToProps() { result = getParameter(0) }

      override API::Node getMapDispatchToProps() { result = getParameter(1) }
    }

    private DataFlow::CallNode heuristicConnectCall() {
      result.getAnArgument().asExpr().(Identifier).getName() =
        ["mapStateToProps", "mapDispatchToProps"] and
      not result = DataFlow::moduleMember("react-redux", "connect").getACall() // exclude genuine calls to avoid duplicate tuples
    }

    /**
     * An entry point in the API graphs corresponding to functions named `mapDispatchToProps`,
     * used to catch cases where the call to `connect` was not found (usually because of it being
     * wrapped in another function, which API graphs won't look through).
     */
    private class HeuristicConnectEntryPoint extends API::EntryPoint {
      HeuristicConnectEntryPoint() { this = "react-redux-connect" }

      override DataFlow::Node getARhs() { none() }

      override DataFlow::SourceNode getAUse() {
        result = heuristicConnectCall().getCalleeNode().getALocalSource()
      }
    }

    private class HeuristicConnectFunction extends ConnectCall {
      HeuristicConnectFunction() {
        this = API::root().getASuccessor(any(HeuristicConnectEntryPoint e)).getACall()
      }

      override API::Node getMapStateToProps() {
        result = getAParameter() and
        result.getARhs().asExpr().(Identifier).getName() = "mapStateToProps"
      }

      override API::Node getMapDispatchToProps() {
        result = getAParameter() and
        result.getARhs().asExpr().(Identifier).getName() = "mapDispatchToProps"
      }
    }

    /**
     * A call to `connect()`, typically as part of a code pattern like the following:
     * ```js
     * let withConnect = connect(mapStateToProps, mapDispatchToProps);
     * let MyAwesomeComponent = compose(withConnect, otherStuff)(MyComponent);
     * ```
     */
    abstract private class ConnectCall extends API::CallNode {
      abstract API::Node getMapStateToProps();

      abstract API::Node getMapDispatchToProps();

      /**
       * Gets a function whose first argument becomes the React component to connect.
       */
      DataFlow::SourceNode getAComponentTransformer() {
        result = this
        or
        exists(FunctionCompositionCall compose |
          getAComponentTransformer().flowsTo(compose.getAnOperandNode()) and
          result = compose
        )
      }

      /**
       * Gets a data-flow node that should flow to `props.name` via the `mapDispatchToProps` function.
       */
      DataFlow::Node getDispatchPropNode(string name) {
        // TODO not currently used
        result = getMapDispatchToProps().getMember(name).getARhs()
        or
        exists(BindActionCreatorsCall bind |
          bind.flowsTo(getMapDispatchToProps().getReturn().getARhs()) and
          result = bind.getOptionArgument(0, name)
        )
      }

      /**
       * Gets the React component decorated by this call, if one can be determined.
       */
      ReactComponent getReactComponent() {
        result
            .getAComponentCreatorReference()
            .flowsTo(getAComponentTransformer().getACall().getArgument(0))
      }
    }

    predicate stateToPropsStep(DataFlow::Node pred, DataFlow::Node succ) {
      exists(ConnectCall call |
        pred = call.getMapStateToProps().getReturn().getARhs() and
        succ = call.getReactComponent().getADirectPropsAccess()
      )
    }

    predicate dispatchToPropsStep(DataFlow::Node pred, DataFlow::Node succ) {
      exists(ConnectCall call, string member |
        pred = call.getDispatchPropNode(member) and
        succ = call.getReactComponent().getAPropRead(member)
      )
    }

    private class ConnectionStep extends DataFlow::AdditionalFlowStep {
      ConnectionStep() { this instanceof ConnectCall }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        exists(ConnectCall connect | connect = this |
          pred = connect.getMapStateToProps().getReturn().getARhs() and
          succ = connect.getReactComponent().getADirectPropsAccess()
          or
          // Boost property depth tracking
          exists(string name |
            pred = connect.getMapStateToProps().getReturn().getMember(name).getARhs() and
            succ = connect.getReactComponent().getAPropRead(name)
          )
        )
      }
    }

    private class MapDispatchToPropsArg extends DispatchFunctionSource {
      MapDispatchToPropsArg() {
        // If `mapDispatchToProps` is a function, its first argument is `dispatch`
        this = any(ConnectCall c).getMapDispatchToProps().getParameter(0).getAnImmediateUse()
      }
    }

    private class MapDispatchToPropsMember extends DispatchedValueSink {
      MapDispatchToPropsMember() {
        // If `mapDispatchToProps` is an object, each method will have its result dispatched
        this = any(ConnectCall c).getMapDispatchToProps().getAMember().getReturn().getARhs()
      }
    }

    private class MapStateToPropsStateSource extends RootStateNode {
      MapStateToPropsStateSource() {
        this = any(ConnectCall c).getMapStateToProps().getParameter(0)
      }
    }
  }

  module Reselect {
    class CreateSelectorCall extends API::CallNode {
      CreateSelectorCall() {
        this = API::moduleImport(["reselect", "@reduxjs/toolkit"]).getMember("createSelector").getACall()
      }

      API::Node getSelectorFunction(int i) {
        // When there are multiple callbacks, exclude the last one
        result = getParameter(i) and
        (i = 0 or i < getNumArgument() - 1)
        or
        exists(DataFlow::ArrayCreationNode array |
          array.flowsTo(getArgument(0)) and
          result.getAUse() = array.getElement(i)
        )
      }
    }

    /** The state argument to a selector */
    private class SelectorStateArg extends RootStateNode {
      SelectorStateArg() { this = any(CreateSelectorCall c).getSelectorFunction(_).getParameter(0) }
    }

    predicate selectorStep(DataFlow::Node pred, DataFlow::Node succ) {
      // Return value of `i`th callback flows to the `i`th parameter of the last callback.
      exists(CreateSelectorCall call, int index |
        call.getNumArgument() > 1 and
        pred = call.getSelectorFunction(index).getReturn().getARhs() and
        succ = call.getLastParameter().getParameter(index).getAnImmediateUse()
      )
      or
      // The result of the last callback is the final result
      exists(CreateSelectorCall call |
        pred = call.getLastParameter().getReturn().getARhs() and
        succ = call
      )
    }

    class SelectorStep extends DataFlow::AdditionalFlowStep {
      SelectorStep() { selectorStep(_, this) }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        selectorStep(pred, succ) and
        this = succ
      }
    }
  }

  module Debbugging {
    predicate missedDispatch(DataFlow::SourceNode node) {
      // Many originally missed in grafana due to thunks in mapDispatchToProps functions, but found now
      // Still missing navigateToExplore due to: possibly unresolved import?
      node.asExpr().(Identifier).getName() = "dispatch" and
      not node = getADispatchFunctionReference()
    }

    predicate missedReducerUse(DataFlow::SourceNode node) {
      node.flowsToExpr(any(Identifier id | id.getName().regexpMatch("(?i).*reducer"))) and
      not node = any(ReducerArg arg).getASource()
    }

    predicate missedReducerFunction(DataFlow::FunctionNode function) {
      function.getParameter(0).getName() = "state" and
      (
        function.getParameter(1).getName() = "action"
        or
        exists(function.getParameter(1).getAPropertyRead("payload"))
      ) and
      not function = any(ReducerArg arg).getASource()
    }

    predicate missedPayloadSource(DataFlow::PropRead payload) {
      payload.getPropertyName() = "payload" and
      not payload = any(ActionCreator c).getAPayloadReference()
    }

    predicate unconnectedReducer(DelegatingReducer r) {
      // Findings:
      //   'workspaceReducer' in graphql-playground: manually invoked with state.getIn(['workspace', blah])
      //   combineReducers in Signal-Destop, not sure why
      not exists(r.getUseSite())
    }

    predicate test(DataFlow::PropWrite write, string name) {
      name = write.getPropertyNameExpr().getStringValue()
    }
  }
}
