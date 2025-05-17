private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean
private import codeql.util.Unit
private import codeql.ssa.Ssa as Ssa
private import codeql.dataflow.VariableCapture as VariableCapture

module LanguageDataFlow<
  LocationSig Location, LanguageBaseSig<Location> Base, LanguageCommonSig<Location, Base> Common>
{
  private import Base
  private import Common
  private import MakeLanguageBase<Location, Base>
  private import MakeLanguageCommon<Location, Base, Common>

  signature module LanguageDataFlowSig {
    class LocalVariable {
      VariableReference getAReference();

      string toString();

      Location getLocation();

      Common::CfgScope getCfgScope();

      predicate isCaptured();
    }

    class VariableReference extends Base::AstNode;

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
        // TODO: map too-large indices to a lower bound content set
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
        TValue() or
        TTaint() or
        TRead(ContentSet contents) or
        TStore(ContentSet contents) or
        TWithContent(ContentSet contents) or
        TWithoutContent(ContentSet contents)

      class Step extends TStep {
        bindingset[this]
        Step() { any() } // Help catch some bugs in pracitce

        predicate value() { this = TValue() }

        predicate taint() { this = TTaint() }

        predicate read(ContentSet contents) { this = TRead(contents) }

        predicate store(ContentSet contents) { this = TStore(contents) }

        predicate withContent(ContentSet contents) { this = TWithContent(contents) }

        predicate withoutContent(ContentSet contents) { this = TWithoutContent(contents) }

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
            this.withoutContent(contents) and result = "withoutContent(" + contents.toString() + ")"
          )
        }
      }

      class DataFlowBuilder instanceof AstNode {
        bindingset[this]
        DataFlowBuilder() { any() }

        string toString() { result = super.toString() }

        Location getLocation() { result = super.getLocation() }

        predicate isBeingAssignedTo(AstNode node) { this = getLValueNode(node) }

        predicate isValueOf(AstNode node) { this = node }
      }

      signature predicate dataflowStepSig(DataFlowBuilder node1, Step step, DataFlowBuilder node2);

      module Make3<dataflowStepSig/3 dataflowStep> {
        private newtype TDataFlowNode =
          TValueNode(AstNode node) or
          TWithContentHelper(ContentSet contents, AstNode target) {
            dataflowStep(_, TWithContent(contents), target)
          } or
          TWithoutContentHelper(ContentSet contents, AstNode target) {
            dataflowStep(_, TWithoutContent(contents), target)
          } or
          TFlowSummaryNode() // TODO
      }
    }
  }
}
