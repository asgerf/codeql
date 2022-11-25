private import javascript
private import semmle.javascript.dataflow.internal.StepSummary
private import UniversalTypeTrackingImpl

module UniversalTypeTrackingForJavaScript implements UniversalTypeTrackingSig {
  class Node = DataFlow::SourceNode;

  class Content = PropertyName;

  class ContentFilter extends string instanceof DataFlow::PropertySet {
    Content getAMatchingContent() { result = super.getAProperty() }
  }

  private newtype TTransformation =
    MkTransformation(int boundArguments, boolean promisified) {
      boundArguments = [0 .. 10] and
      promisified = [true, false]
    }

  class Transformation extends TTransformation {
    int getNumBoundArguments() { this = MkTransformation(result, _) }

    boolean getPromisified() { this = MkTransformation(_, result) }

    Transformation append(Transformation other) {
      result =
        MkTransformation(this.getNumBoundArguments() + other.getNumBoundArguments(),
          this.getPromisified().booleanOr(other.getPromisified()))
    }

    string toString() { result = "no transformation" }

    predicate isEmpty() { any() }
  }

  Transformation getTransformation(int boundArguments, boolean promisified) {
    result = MkTransformation(boundArguments, promisified)
  }

  pragma[nomagic]
  predicate storeStep(Node pred, Node succ, Content key) {
    StepSummary::step(pred, succ, StoreStep(key))
  }

  pragma[nomagic]
  predicate loadStep(Node pred, Node succ, Content key) {
    StepSummary::step(pred, succ, LoadStep(key))
  }

  pragma[nomagic]
  predicate loadStoreStep(Node pred, Node succ, Content loadKey, Content storeKey) {
    StepSummary::step(pred, succ, LoadStoreStep(loadKey, storeKey))
    or
    StepSummary::step(pred, succ, CopyStep(loadKey)) and
    storeKey = loadKey
  }

  predicate levelStep(Node pred, Node succ) {
    StepSummary::step(pred, succ, LevelStep())
    or
    API::AdditionalUseStep::step(pred, succ)
    or
    extraDefStep(pred, succ)
  }

  private predicate extraDefStep(Node pred, Node succ) {
    // additional backwards step from `require('m')` to `exports` or `module.exports` in m
    exists(Import imp | succ = imp.getImportedModuleNode() |
      pred = DataFlow::exportsVarNode(imp.getImportedModule())
      or
      pred = DataFlow::moduleVarNode(imp.getImportedModule()).getAPropertyRead("exports")
    )
    or
    exists(ObjectExpr obj |
      succ.asExpr() = obj and
      pred =
        obj.getAProperty()
            .(SpreadProperty)
            .getInit()
            .(SpreadElement)
            .getOperand()
            .flow()
            .getALocalSource()
    )
  }

  predicate callStep(Node pred, Node succ) {
    StepSummary::step(pred, succ, CallStep()) and
    not succ instanceof DataFlow::ThisNode
  }

  predicate withContentStep(Node pred, Node succ, ContentFilter filter) { none() }

  predicate withoutContentStep(Node pred, Node succ, ContentFilter filter) {
    StepSummary::step(pred, succ, WithoutPropStep(filter))
  }

  predicate returnStep(Node pred, Node succ) { StepSummary::step(pred, succ, ReturnStep()) }

  predicate jumpStep(Node pred, Node succ) { none() }

  predicate transformStep(Node pred, Node succ, Transformation transform) {
    exists(DataFlow::PartialInvokeNode invoke, int boundArgs |
      succ = invoke.getBoundFunction(pred, boundArgs) and
      transform = MkTransformation(boundArgs, false)
    )
    or
    exists(Promisify::PromisifyCall promisify |
      pred = promisify.getArgument(0) and
      succ = promisify and
      transform = MkTransformation(0, true)
    )
  }

  predicate isParameterLike(Node node) { node instanceof DataFlow::ParameterNode }

  predicate isSelfParameter(Node node) { node instanceof DataFlow::ThisNode }

  predicate shouldTrack(Node node) { any() }
}

module UniversalTypeTracking = UniversalTypeTrackingGen<UniversalTypeTrackingForJavaScript>;

module ConsistencyChecks {
  private import UniversalTypeTracking
  private import UniversalTypeTrackingForJavaScript

  /** Gets a data flow node referring to a thing. */
  private Node trackReturnValue(DataFlow::TypeTracker t, DataFlow::CallNode call) {
    t.start() and
    result = call
    or
    exists(DataFlow::TypeTracker t2 |
      result = trackReturnValue(t2, call).track(t2, t) and
      not isSelfParameter(result)
    )
  }

  /** Gets a data flow node referring to a thing. */
  Node trackReturnValue(DataFlow::CallNode call) {
    result = trackReturnValue(DataFlow::TypeTracker::end(), call)
  }

  predicate diffFlow(DataFlow::CallNode call, Node to, string diff) {
    to = trackReturnValue(call) and
    not trackNode(call) = to and
    diff = "lost"
    or
    trackNode(call) = to and
    not trackReturnValue(call) = to and
    diff = "gained"
  }
}
