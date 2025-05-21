private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import LanguageCfg
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean
private import codeql.util.Unit
private import codeql.ssa.Ssa as Ssa
private import codeql.dataflow.VariableCapture as VariableCapture
private import codeql.dataflow.DataFlow as DataFlow

module LanguageDataFlow<
  LocationSig Location, LanguageBaseSig<Location> Base, LanguageCommonSig<Location, Base> Common>
{
  private import Base
  private import Common
  private import MakeLanguageBase<Location, Base>
  private import MakeLanguageCommon<Location, Base, Common>

  final private class FinalAstNode = AstNode;

  signature module LanguageDataFlowSig {
    class LocalVariable {
      VariableReference getAReference();

      string toString();

      Location getLocation();

      Common::CfgScope getCfgScope();

      predicate isCaptured();
    }

    class VariableReference extends Base::AstNode;

    default predicate assignmentIsUncertain(Base::SyntheticNode lvalueNode) { none() }

    default predicate readIsUncertain(VariableReference ref) { none() }

    default predicate definitelyInitialized(LocalVariable v) { none() }

    class Constant {
      int asArrayIndex();

      /** Gets the operand used when referencing this constant from a MaD token. */
      string getAsOperand();

      /** Gets a string-representation of the constant. Should generally equal `getAsOperand()` when that exists. */
      string toString();
    }

    /**
     * A type of container that associates values with a key or index, such as arrays, lists, tuples, maps, dictionaries, etc.
     *
     * In some languages, lists and maps may be difficult to distinguish at their use sites as they are interacted with using the same syntax or method names.
     * In such cases it can make sense to unify the relevant container kinds.
     *
     * Non-indexable containers such as sets, iterators, and streams should either be represented by a `LanguageContent`, or be treated interchangeably
     * with the contents of another container kind. For example: iterator contents could be represented by array contents, so the conversion between
     * arrays and iterators becomes a no-op. In other languages it may be better for it to have its own `LanguageContent`. The choice depends on how
     * difficult it is to recognise conversions between the container kinds, versus the value of pruning false flow based on more fine-grained contents.
     */
    class IndexedContainerKind {
      /** Holds if data flowing into the keys themselves should be tracked. For array-like containers this should be `none()`. */
      predicate trackFlowIntoKeys();

      /** Gets the MaD token to associate with keys in this map-like container. Should have no result for array-like containers. */
      string getKeyToken();

      /** Gets the MaD token to associate with values in this container (i.e. map values or array elements). */
      string getValueToken();

      /**
       * Holds if values that are associated with `key` should be tracked precisely.
       *
       * For array-like containers, this should hold for non-negative integers up to a certain size.
       *
       * For map-like containers, this should hold for all keys that are likely worth tracking.
       */
      predicate trackValuesAssociatedWithKey(Constant key);
    }

    /**
     * A language-specific content that is not handled by `IndexedContainerKind`.
     */
    class LanguageContent {
      predicate hasMadToken(string head, string operand);

      string toString();

      Location getLocation();
    }

    class ClosureExpr extends AstNode {
      predicate hasBody(CfgScope scope);
    }
  }

  module Make1<LanguageDataFlowSig D> {
    private import D

    private newtype TContent =
      TCaptureContent(LocalVariable v) { v.isCaptured() } or
      TContainerSlot(IndexedContainerKind kind, Constant key) {
        kind.trackValuesAssociatedWithKey(key)
      } or
      TContainerUnknownSlot(IndexedContainerKind kind) or
      TContainerKey(IndexedContainerKind kind) { kind.trackFlowIntoKeys() } or
      TLanguageContent(LanguageContent kind)

    class Content extends TContent {
      LocalVariable asCapturedVariable() { this = TCaptureContent(result) }

      Constant asContainerSlot(IndexedContainerKind kind) { this = TContainerSlot(kind, result) }

      int asArrayIndex(IndexedContainerKind kind) {
        result = this.asContainerSlot(kind).asArrayIndex()
      }

      predicate isUnknownContainerSlot(IndexedContainerKind kind) {
        this = TContainerUnknownSlot(kind)
      }

      predicate isContainerKey(IndexedContainerKind kind) { this = TContainerKey(kind) }

      LanguageContent asLanguageContent() { this = TLanguageContent(result) }

      string toString() {
        // Note: these strings are visible to end-users in the generated data flow paths.
        result = this.asCapturedVariable().toString()
        or
        exists(IndexedContainerKind kind |
          result = kind.getValueToken() + "[" + this.asContainerSlot(kind).toString() + "]"
          or
          this.isUnknownContainerSlot(kind) and
          result = kind.getValueToken()
          or
          this.isContainerKey(kind) and
          result = kind.getKeyToken()
        )
        or
        result = this.asLanguageContent().toString()
      }

      Location getLocation() {
        result = this.asCapturedVariable().getLocation()
        or
        result = this.asLanguageContent().getLocation()
      }
    }

    signature class LanguageContentSetSig {
      Content getAReadContent();

      Content getAStoreContent();

      predicate hasMadToken(string head, string operand);

      string toString();

      Location getLocation();
    }

    module Make2<LanguageContentSetSig LanguageContentSet> {
      private newtype TContentSet =
        TSingleton(TContent content) or
        TContainerKnownSlot(IndexedContainerKind kind, Constant key) {
          kind.trackValuesAssociatedWithKey(key)
        } or
        TArrayElementLowerBound(IndexedContainerKind kind, int bound) {
          exists(Constant key |
            kind.trackValuesAssociatedWithKey(key) and
            bound = key.asArrayIndex()
          )
        } or
        TContainerAnySlot(IndexedContainerKind kind) or
        TLanguageContentSet(LanguageContentSet contents)

      class ContentSet extends TContentSet {
        Content asSingleton() { this = TSingleton(result) }

        Constant asContainerSlot(IndexedContainerKind kind) {
          this = TContainerKnownSlot(kind, result)
        }

        predicate isAnyContainerSlot(IndexedContainerKind kind) { this = TContainerAnySlot(kind) }

        int asArrayElementLowerBound(IndexedContainerKind kind) {
          this = TArrayElementLowerBound(kind, result)
        }

        LanguageContentSet asLanguageContentSet() { this = TLanguageContentSet(result) }

        string toString() {
          result = this.asSingleton().toString()
          or
          exists(IndexedContainerKind kind |
            result = kind.getValueToken() + "[" + this.asArrayElementLowerBound(kind) + "..]"
            or
            result = kind.getValueToken() + "[" + this.asContainerSlot(kind) + "]"
            or
            this.isAnyContainerSlot(kind) and
            result = kind.getValueToken()
          )
          or
          result = this.asLanguageContentSet().toString()
        }

        Location getLocation() { result = this.asLanguageContentSet().getLocation() }

        Content getAReadContent() {
          result = this.asSingleton()
          or
          exists(IndexedContainerKind kind |
            this.asArrayElementLowerBound(kind) <= result.asArrayIndex(kind)
            or
            this.asContainerSlot(kind) = result.asContainerSlot(kind)
            or
            this.isAnyContainerSlot(kind) and
            exists(result.asContainerSlot(kind))
            or
            (
              exists(this.asArrayElementLowerBound(kind)) or
              exists(this.asContainerSlot(kind)) or
              this.isAnyContainerSlot(kind)
            ) and
            result.isUnknownContainerSlot(kind)
          )
          or
          result = this.asLanguageContentSet().getAReadContent()
        }

        Content getAStoreContent() {
          result = this.asSingleton()
          or
          exists(IndexedContainerKind kind |
            result.asContainerSlot(kind) = this.asContainerSlot(kind)
            or
            exists(this.asArrayElementLowerBound(kind)) and
            result.isUnknownContainerSlot(kind) // nothing better can be done at the moment, but this is usually not used for stores anyway
            or
            this.isAnyContainerSlot(kind) and
            result.isUnknownContainerSlot(kind)
          )
          or
          result = this.asLanguageContentSet().getAStoreContent()
        }
      }

      signature class IndexedContainerKindSig extends IndexedContainerKind;

      /** Generates a module with accessors for content sets related to the given array-like container kind. */
      module ArrayContentAccessor<IndexedContainerKindSig Kind> {
        private Kind kind() { any() }

        private Constant preciseKey() { kind().trackValuesAssociatedWithKey(result) }

        private int preciseIndex() { result = preciseKey().asArrayIndex() }

        pragma[nomagic]
        private int maxPreciseIndex() { result = max(preciseIndex()) }

        /** Read from a index or higher. Using this in a store will result in an unknown index. */
        pragma[nomagic]
        ContentSet lowerBound(int index) { result.asArrayElementLowerBound(kind()) = index }

        /** Any element of the array. */
        pragma[nomagic]
        ContentSet anyElement() { result = lowerBound(0) }

        pragma[nomagic]
        private ContentSet maxLowerBound() { result = lowerBound(maxPreciseIndex()) }

        pragma[nomagic]
        private ContentSet knownIndex(int index) {
          result.asContainerSlot(kind()).asArrayIndex() = index
        }

        /**
         * Read or store to a specific index.
         *
         * Reading from this content set will also observe values that were originally stored at an unknown index.
         *
         * Has no result for negative indices. Always has a result for non-negative indices,
         * but indices above a certain threshold will be associated with a less precise content set.
         */
        bindingset[index]
        ContentSet elementAt(int index) {
          result = knownIndex(index)
          or
          // If the index is larger than we can track, use the greatest lower bound instead.
          index > maxPreciseIndex() and
          result = maxLowerBound()
        }

        final private class FinalContentSet = ContentSet;

        /**
         * A singleton content for array elements at a known index, or unknown index.
         *
         * This can be used to generate a set of read and store edges that copy parts
         * of an array to another value. For such purposes, it is best to only rely on
         * singleton (exact) content sets to avoid precision loss.
         *
         * ```codeql
         * exists(Array::ExactContent content |
         *   node1 = ... and
         *   step.read() = content and
         *   node2 = ...
         *   or
         *   node1 = ... and
         *   step.store() = content.shiftUpBy(1) and
         *   node2 = ...
         * )
         * ```
         */
        class ExactContent extends FinalContentSet {
          ExactContent() {
            exists(this.asSingleton().asArrayIndex(kind())) or
            this.asSingleton().isUnknownContainerSlot(kind())
          }

          /** Increase the index by the given value, if it is a known index. */
          bindingset[index]
          ContentSet shiftUpBy(int index) {
            result = elementAt(this.asSingleton().asArrayIndex(kind()) + index)
            or
            this.asSingleton().isUnknownContainerSlot(kind()) and result = this
          }
        }
      }

      /** Generates a module with accessors for the content sets related to the given map-like kind. */
      module MapContentAccessor<IndexedContainerKindSig Kind> {
        private Kind kind() { any() }

        /** One of the keys in a key-value pair stored in a map. */
        pragma[nomagic]
        ContentSet key() { result.asSingleton().isContainerKey(kind()) }

        /** One of the values from a key-value pair stored in a map. */
        pragma[nomagic]
        ContentSet value() { result.isAnyContainerSlot(kind()) }

        pragma[nomagic]
        private ContentSet valueAtExact(Constant key) {
          result.asSingleton().asContainerSlot(kind()) = key
        }

        /**
         * The value associated with `key` in map.
         *
         * If `key` is not one of the keys that are tracked precisely, this will return
         * the same as `value()`.
         */
        bindingset[key]
        ContentSet valueAt(Constant key) {
          result = valueAtExact(key)
          or
          not exists(valueAtExact(key)) and
          result = value()
        }
      }

      private newtype TStep =
        TValueStep() or
        TTaintStep() or
        TReadStep(ContentSet contents) or
        TStoreStep(ContentSet contents) or
        TWithContentStep(ContentSet contents) or
        TWithoutContentStep(ContentSet contents)

      /** Provides classes for constructing data flow steps. */
      module DataFlowBuilder {
        /** A type of data flow type. */
        class Step extends TStep {
          bindingset[this]
          Step() { any() } // Help catch some bugs in pracitce

          predicate value() { this = TValueStep() }

          predicate taint() { this = TTaintStep() }

          predicate read(ContentSet contents) { this = TReadStep(contents) }

          predicate store(ContentSet contents) { this = TStoreStep(contents) }

          predicate withContent(ContentSet contents) { this = TWithContentStep(contents) }

          predicate withoutContent(ContentSet contents) { this = TWithoutContentStep(contents) }

          string toString() {
            this.value() and result = "value"
            or
            this.taint() and result = "taint"
            or
            exists(ContentSet contents |
              this.read(contents) and result = "read(" + contents.toString() + ")"
              or
              this.store(contents) and result = "store(" + contents.toString() + ")"
              or
              this.withContent(contents) and result = "withContent(" + contents.toString() + ")"
              or
              this.withoutContent(contents) and
              result = "withoutContent(" + contents.toString() + ")"
            )
          }
        }

        private class Node instanceof AstNode {
          bindingset[this]
          Node() { any() }

          string toString() { result = super.toString() }

          Location getLocation() { result = super.getLocation() }

          predicate isBeingAssignedTo(AstNode node) { this = getLValueNode(node) }

          predicate isValueOf(AstNode node) { this = node }
        }

        /** A node that can be used as the source of a data flow step. */
        class Node1 = Node;

        /** A node that can be used as the destination of a data flow step. */
        class Node2 = Node;

        signature predicate dataflowStepSig(Node1 node1, Step step, Node2 node2);
      }

      private import LanguageCfgBuilder<Location, Base, Common>

      module Make3<DataFlowBuilder::dataflowStepSig/3 dataflowStep, LanguageCfgSig CfgSig> {
        private import MakeLanguageCfg<CfgSig>

        final private class FinalLocalVariable = LocalVariable;

        /**
         * Instantiation of SSA for non-captured variables.
         */
        private module LocalSsaConfig implements Ssa::InputSig<Location> {
          class BasicBlock = BasicBlocks::BasicBlock;

          class ControlFlowNode = AstNode;

          BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) {
            result.immediatelyDominates(bb)
          }

          BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

          class SourceVariable extends FinalLocalVariable {
            SourceVariable() { not this.isCaptured() }
          }

          pragma[nomagic]
          private BasicBlock getEntryBlock(CfgScope scope) {
            result.getANode() = getCfgEntryPoint(scope)
          }

          predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
            exists(AstNode lvalueNode |
              lvalueNode = getLValueNode(v.getAReference()) and
              bb.getNode(i) = lvalueNode and
              if assignmentIsUncertain(lvalueNode) then certain = false else certain = true
            )
            or
            // For variables that are not definitely initialized, put a synthetic initializer in the entry block
            not definitelyInitialized(v) and
            bb = getEntryBlock(v.getCfgScope()) and
            i = -1 and
            certain = true
          }

          predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
            exists(AstNode ref |
              ref = v.getAReference() and
              not isInPureLValuePosition(ref) and // not a read if pure lvalue
              bb.getNode(i) = ref and
              if readIsUncertain(ref) then certain = false else certain = true
            )
          }
        }

        private module LocalSsa = Ssa::Make<Location, LocalSsaConfig>;

        private module LocalSsaDataFlowConfig implements LocalSsa::DataFlowIntegrationInputSig {
          class Expr extends FinalAstNode {
            predicate hasCfgNode(BasicBlock bb, int i) { this = bb.getNode(i) }
          }

          class Guard extends FinalAstNode {
            Guard() { isCondition(this) }

            BasicBlock getOutcomeBlock(boolean branch) {
              result.getANode() = getConditionalOutcomeNode(this, branch)
            }

            predicate controlsBranchEdge(BasicBlock bb1, BasicBlock bb2, boolean branch) {
              bb1.getNode(_) = this and
              bb2 = this.getOutcomeBlock(branch)
            }
          }

          predicate guardDirectlyControlsBlock(Guard guard, BasicBlock bb, boolean branch) {
            guard.getOutcomeBlock(branch).dominates(bb)
          }

          predicate includeWriteDefsInFlowStep() { none() } // not needed as we have lvalue nodes already
        }

        private module LocalSsaDataFlow = LocalSsa::DataFlowIntegration<LocalSsaDataFlowConfig>;

        predicate valueStep(AstNode node1, AstNode node) { dataflowStep(node1, TValueStep(), node) }

        pragma[nomagic]
        private LocalVariable getCapturedVariableFromLValue(SyntheticNode lvalue) {
          result.isCaptured() and
          lvalue = getLValueNode(result.getAReference())
        }

        /** Holds if `node1 -> node2` steps from a write of a captured variable to any of its reads. */
        bindingset[node1]
        pragma[inline_late]
        predicate captureStepApprox(SyntheticNode node1, VariableReference node2) {
          exists(LocalVariable v |
            v = getCapturedVariableFromLValue(node1) and
            node2 = v.getAReference() and
            not isInPureLValuePosition(node2)
          )
        }

        predicate closureExprHasAliasExpr(ClosureExpr expr, AstNode alias) {
          alias = expr
          or
          exists(AstNode pred | closureExprHasAliasExpr(expr, pred) |
            valueStep(pred, alias)
            or
            captureStepApprox(pred, alias)
          )
          or
          exists(LocalSsa::Definition def, LocalVariable v, BasicBlock bb, int i |
            closureExprHasAliasSsa(expr, def) and
            LocalSsa::ssaDefReachesRead(v, def, bb, i) and
            bb.getNode(i) = alias and
            v.getAReference() = alias
          )
        }

        predicate closureExprHasAliasSsa(ClosureExpr expr, LocalSsa::Definition alias) {
          exists(BasicBlock bb, int i |
            closureExprHasAliasExpr(expr, bb.getNode(i)) and
            alias.(LocalSsa::WriteDefinition).definesAt(_, bb, i)
          )
          or
          exists(LocalSsa::Definition prev, LocalVariable v, BasicBlock bb, int i |
            closureExprHasAliasSsa(expr, prev) and
            LocalSsa::ssaDefReachesRead(v, prev, bb, i) and
            alias.definesAt(v, bb, i)
          )
        }

        module VariableCaptureConfig implements VariableCapture::InputSig<Location> {
          class BasicBlock extends BasicBlocks::BasicBlock {
            Callable getEnclosingCallable() { result = this.getScope() }
          }

          class ControlFlowNode = AstNode;

          BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) {
            result.immediatelyDominates(bb)
          }

          BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

          class CapturedVariable extends FinalLocalVariable {
            CapturedVariable() { this.isCaptured() }

            /** Gets the callable that defines this variable. */
            Callable getCallable() { result = this.getCfgScope() }
          }

          class CapturedParameter extends CapturedVariable {
            CapturedParameter() { none() } // Not needed here, as parameters and local variable writes (lvalues) are separate nodes
          }

          class Expr extends FinalAstNode {
            /** Holds if the `i`th node of basic block `bb` evaluates this expression. */
            predicate hasCfgNode(BasicBlock bb, int i) { bb.getNode(i) = this }
          }

          class VariableWrite extends Expr {
            private CapturedVariable v;
            private VariableReference ref;

            VariableWrite() {
              this = getLValueNode(ref) and
              v.getAReference() = ref
            }

            CapturedVariable getVariable() { result = v }
          }

          final private class FinalVariableReference = VariableReference;

          class VariableRead extends Expr, FinalVariableReference {
            private CapturedVariable v;

            VariableRead() { this = v.getAReference() and not isInPureLValuePosition(this) }

            CapturedVariable getVariable() { result = v }
          }

          final private class FinalClosureExprBase = D::ClosureExpr;

          class ClosureExpr extends Expr, FinalClosureExprBase {
            predicate hasAliasedAccess(Expr f) { closureExprHasAliasExpr(this, f) }

            predicate hasBody(Callable callable) { FinalClosureExprBase.super.hasBody(callable) }
          }

          final private class FinalCfgScope = CfgScope;

          class Callable extends FinalCfgScope {
            predicate isConstructor() {
              none() // TODO
            }
          }
        }

        private module CaptureSsa = VariableCapture::Flow<Location, VariableCaptureConfig>;

        newtype TDataFlowNode =
          TValueNode(AstNode node) or
          TWithContentHelper(ContentSet contents, AstNode target) {
            dataflowStep(_, TWithContentStep(contents), target)
          } or
          TWithoutContentHelper(ContentSet contents, AstNode target) {
            dataflowStep(_, TWithoutContentStep(contents), target)
          } or
          TLocalSsaNode(LocalSsaDataFlow::SsaNode node) or
          TCaptureSsaNode(CaptureSsa::SynthesizedCaptureNode node) or
          TFlowSummaryNode() // TODO

        class DataFlowNode extends TDataFlowNode {
          pragma[nomagic]
          AstNode asAstNode() { this = TValueNode(result) }

          /** Holds if this represents the value abut to be assigned to the given `lvalue`. */
          predicate isValueBeingAssignedTo(AstNode lvalue) {
            this.asAstNode() = getLValueNode(lvalue)
          }

          string toString() {
            result = this.asAstNode().toString()
            or
            exists(ContentSet contents, AstNode target |
              this = TWithContentHelper(contents, target) and
              result = "withContent " + contents + " " + target
            )
            or
            exists(ContentSet contents, AstNode target |
              this = TWithoutContentHelper(contents, target) and
              result = "withoutContent " + contents + " " + target
            )
            or
            exists(LocalSsaDataFlow::SsaNode node |
              this = TLocalSsaNode(node) and
              result = "SSA " + node
            )
            or
            exists(CaptureSsa::SynthesizedCaptureNode node |
              this = TCaptureSsaNode(node) and
              result = "Capture " + node
            )
            or
            this = TFlowSummaryNode() and
            result = "FlowSummaryNode"
          }

          Location getLocation() {
            result = this.asAstNode().getLocation()
            or
            exists(ContentSet contents, AstNode target |
              this = TWithContentHelper(contents, target) and
              result = target.getLocation()
            )
            or
            exists(ContentSet contents, AstNode target |
              this = TWithoutContentHelper(contents, target) and
              result = target.getLocation()
            )
            or
            exists(LocalSsaDataFlow::SsaNode node |
              this = TLocalSsaNode(node) and
              result = node.getLocation()
            )
            or
            exists(CaptureSsa::SynthesizedCaptureNode node |
              this = TCaptureSsaNode(node) and
              result = node.getLocation()
            )
          }
        }

        private AstNode getPostUpdateNode(AstNode node) {
          none() // TODO
        }

        bindingset[node]
        pragma[inline_late]
        private DataFlowNode getNodeFromLocalSsa(LocalSsaDataFlow::Node node) {
          result = TLocalSsaNode(node) // Note: only holds for SsaNode subclass
          or
          result.asAstNode() = node.(LocalSsaDataFlow::ExprNode).getExpr()
          or
          exists(BasicBlock bb, int i |
            node.(LocalSsaDataFlow::WriteDefSourceNode).getDefinition().definesAt(_, bb, i) and
            result.asAstNode() = bb.getNode(i) // Gets the LValue node
          )
          or
          result.asAstNode() =
            getPostUpdateNode(node.(LocalSsaDataFlow::ExprPostUpdateNode).getExpr())
        }

        bindingset[node]
        pragma[inline_late]
        private DataFlowNode getNodeFromCaptureSsa(CaptureSsa::ClosureNode node) {
          result = TCaptureSsaNode(node) // Note: only holds for SynthesizedCaptureNode subclass
          or
          result.asAstNode() = node.(CaptureSsa::ExprNode).getExpr()
          or
          result.asAstNode() = node.(CaptureSsa::VariableWriteSourceNode).getVariableWrite() // Gets the LValue node
          or
          result.asAstNode() = getPostUpdateNode(node.(CaptureSsa::ExprPostUpdateNode).getExpr())
        }

        predicate localFlowStep(DataFlowNode node1, DataFlowNode node2) {
          dataflowStep(node1.asAstNode(), TValueStep(), node2.asAstNode())
          or
          // With/WithoutContentHelpers are intermediate nodes with expects/clearsContent
          // and a value step to their intended target node.
          exists(AstNode source, ContentSet contents, AstNode target |
            dataflowStep(source, TWithContentStep(contents), target)
          |
            node1.asAstNode() = source and
            node2 = TWithContentHelper(contents, target)
            or
            node1 = TWithContentHelper(contents, target) and
            node2.asAstNode() = target
          )
          or
          exists(AstNode source, ContentSet contents, AstNode target |
            dataflowStep(source, TWithoutContentStep(contents), target)
          |
            node1.asAstNode() = source and
            node2 = TWithoutContentHelper(contents, target)
            or
            node1 = TWithoutContentHelper(contents, target) and
            node2.asAstNode() = target
          )
          or
          exists(LocalSsaDataFlow::Node n1, LocalSsaDataFlow::Node n2 |
            LocalSsaDataFlow::localFlowStep(_, n1, n2, _) and
            node1 = getNodeFromLocalSsa(n1) and
            node2 = getNodeFromLocalSsa(n2)
          )
          or
          exists(CaptureSsa::ClosureNode n1, CaptureSsa::ClosureNode n2 |
            CaptureSsa::localFlowStep(n1, n2) and
            node1 = getNodeFromCaptureSsa(n1) and
            node2 = getNodeFromCaptureSsa(n2)
          )
        }

        predicate readStep(DataFlowNode node1, ContentSet contents, DataFlowNode node2) {
          dataflowStep(node1.asAstNode(), TReadStep(contents), node2.asAstNode())
          or
          exists(CaptureSsa::ClosureNode n1, CaptureSsa::ClosureNode n2 |
            CaptureSsa::readStep(n1, contents.asSingleton().asCapturedVariable(), n2) and
            node1 = getNodeFromCaptureSsa(n1) and
            node2 = getNodeFromCaptureSsa(n2)
          )
        }

        predicate storeStep(DataFlowNode node1, ContentSet contents, DataFlowNode node2) {
          dataflowStep(node1.asAstNode(), TStoreStep(contents), node2.asAstNode())
          or
          exists(CaptureSsa::ClosureNode n1, CaptureSsa::ClosureNode n2 |
            CaptureSsa::storeStep(n1, contents.asSingleton().asCapturedVariable(), n2) and
            node1 = getNodeFromCaptureSsa(n1) and
            node2 = getNodeFromCaptureSsa(n2)
          )
        }

        predicate clearsContent(DataFlowNode node, ContentSet contents) {
          node = TWithoutContentHelper(contents, _)
        }

        predicate expectsContent(DataFlowNode node, ContentSet contents) {
          node = TWithContentHelper(contents, _)
        }
        // private module DataFlowInput implements DataFlow::InputSig<Location> {
        //   class Node = DataFlowNode;
        // }
      }
    }
  }
}
