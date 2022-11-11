private import semmle.python.dataflow.new.DataFlow
private import DataFlowPrivate as Private
private import TypeTrackerSpecific as TT
private import UniversalTypeTrackingImpl

/**
 * Module providing language-specific configuration to `CoarseFlow`.
 *
 * It written like this to simplify eventual migration to a parameterized module,
 * though it's not 100% ready to be parameterized yet.
 */
module UniversalTypeTrackingForPython implements UniversalTypeTrackingSig {
  class Node = TT::TypeTrackingNode;

  class Content = TT::TypeTrackerContent;

  class ContentFilter = TT::ContentFilter;

  pragma[nomagic]
  predicate storeStep(Node pred, Node succ, Content key) {
    TT::basicStoreStep(pred.getALocalUse(), succ.getALocalUse(), key)
  }

  pragma[nomagic]
  predicate loadStep(Node pred, Node succ, Content key) {
    TT::basicLoadStep(pred.getALocalUse(), succ, key)
  }

  pragma[nomagic]
  predicate loadStoreStep(Node pred, Node succ, Content loadKey, Content storeKey) {
    TT::basicLoadStoreStep(pred.getALocalUse(), succ.getALocalUse(), loadKey, storeKey)
  }

  predicate levelStep(Node pred, Node succ) {
    TT::levelStepCall(pred.getALocalUse(), succ)
    or
    TT::levelStepNoCall(pred.getALocalUse(), succ)
    or
    pred.flowsTo(succ) and
    pred != succ
  }

  predicate callStep(Node pred, Node succ) {
    TT::callStep(pred.getALocalUse(), succ) and
    not isSelfParameter(succ)
  }

  predicate withContentStep(Node pred, Node succ, TT::ContentFilter filter) {
    TT::basicWithContentStep(pred.getALocalUse(), succ, filter)
  }

  predicate withoutContentStep(Node pred, Node succ, TT::ContentFilter filter) {
    TT::basicWithoutContentStep(pred.getALocalUse(), succ, filter)
  }

  predicate returnStep(Node pred, Node succ) { TT::returnStep(pred.getALocalUse(), succ) }

  predicate jumpStep(Node pred, Node succ) { TT::jumpStep(pred.getALocalUse(), succ) }

  predicate isParameterLike(Node node) { node instanceof DataFlow::ParameterNode }

  predicate isSelfParameter(Node node) {
    node.(DataFlow::ParameterNode).getParameter().getName() = "self"
  }

  predicate shouldTrack(Node node) { any() }
}

module UniversalTypeTracking = UniversalTypeTrackingGen<UniversalTypeTrackingForPython>;

module ConsistencyChecks {
  private import UniversalTypeTracking
  private import UniversalTypeTrackingForPython
  private import semmle.python.dataflow.new.TypeTracker as T

  class CallNode extends DataFlow::Node {
    CallNode() { this.asCfgNode().isCall() }
  }

  /** Gets a data flow node referring to a thing. */
  private Node trackReturnValue(T::TypeTracker t, CallNode call) {
    t.start() and
    result = call
    or
    exists(T::TypeTracker t2 |
      result = trackReturnValue(t2, call).track(t2, t) and
      not isSelfParameter(result)
    )
  }

  /** Gets a data flow node referring to a thing. */
  Node trackReturnValue(CallNode call) { result = trackReturnValue(T::TypeTracker::end(), call) }

  predicate diffFlow(CallNode call, Node to, string diff) {
    to = trackReturnValue(call) and
    not trackNode(call) = to and
    diff = "lost"
    or
    trackNode(call) = to and
    not trackReturnValue(call) = to and
    diff = "gained"
  }
}
