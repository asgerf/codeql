private import codeql.util.Location
private import LanguageBase
private import LanguageCommon
private import codeql.controlflow.BasicBlock as BB
private import codeql.util.Boolean
private import codeql.util.Unit
private import codeql.ssa.Ssa as Ssa
private import codeql.dataflow.VariableCapture as VariableCapture

signature module LanguageDataFlowSig<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C>
{
  class LocalVariable {
    VariableReference getAReference();

    string toString();

    Location getLocation();

    C::CfgScope getCfgScope();

    predicate isCaptured();
  }

  class VariableReference extends L::AstNode;

  /**
   * Kind of array-like container in this language.
   *
   * For example:
   * - Python: lists and tuples
   * - Java: native arrays, and List-like collection
   * - JS: arrays
   */
  class ArrayKind {
    /** Gets the MaD token to use for this array kind, such as `ArrayElement`. */
    string getToken();
  }

  /**
   * Gets the largest index track precisely in an array of the given kind.
   *
   * This can be -1 if no index should be tracked precisely.
   */
  default int getMaxPreciseIndex(ArrayKind kind) { result = 10 }

  /**
   * Kind of map or dictionary container in this language.
   */
  class MapKind {
    /** Gets the MaD token to use for the keys of this dictionary, such as `MapKey`. */
    string getKeyToken();

    /** Gets the MaD token to use for the values of this dictionary, such as `MapValue`. */
    string getValueToken();

    /** Holds if `key` is a valid to track in maps of this kind. */
    predicate isValidKnownKey(MapKey key);
  }

  /** A constant value that may be tracked precisely as the key in a map-like object. */
  class MapKey {
    string toString();

    /** Gets the operand to appear in the `MapKey`-token */
    string getMadOperand();
  }

  /**
   * A language-specific content that is not array-like or map-like. For example:
   * - The contents of a field declared in user code
   * - The contents of an iterator, stream, or set, if these are not interchangeable with arrays in practice.
   */
  class LanguageContent {
    predicate hasMadToken(string head, string operand);

    string toString();

    Location getLocation();
  }
}

module LanguageDataFlow<
  LocationSig Location, LanguageBaseSig<Location> L, LanguageCommonSig<Location, L> C,
  LanguageDataFlowSig<Location, L, C> D>
{
  private import L
  private import C
  private import D
  private import MakeLanguageBase<Location, L>
  private import MakeLanguageCommon<Location, L, C>

  private newtype TContent =
    TCaptureContent(LocalVariable v) { v.isCaptured() } or
    TArrayElementIndex(ArrayKind kind, int n) { n = [0 .. getMaxPreciseIndex(kind)] } or
    TArrayElementUnknown(ArrayKind kind) or
    TMapKey(MapKind kind) or
    TMapValueWithKnownKey(MapKind kind, MapKey key) { kind.isValidKnownKey(key) } or
    TMapValueWithUnknownKey(MapKind kind) or
    TLanguageContent(LanguageContent kind)

  class Content extends TContent {
    LocalVariable asCapturedVariable() { this = TCaptureContent(result) }

    int asArrayIndex(ArrayKind kind) { this = TArrayElementIndex(kind, result) }

    predicate isUnknownArrayElement(ArrayKind kind) { this = TArrayElementUnknown(kind) }

    predicate isMapKey(MapKind kind) { this = TMapKey(kind) }

    MapKey asMapValueWithKnownKey(MapKind kind) { this = TMapValueWithKnownKey(kind, result) }

    predicate isUnknownMapValue(MapKind kind) { this = TMapValueWithUnknownKey(kind) }

    LanguageContent asLanguageContent() { this = TLanguageContent(result) }

    string toString() {
      // Note: these strings are visible to end-users in the generated data flow paths.
      result = this.asCapturedVariable().toString()
      or
      exists(ArrayKind kind |
        result = kind.getToken() + "[" + this.asArrayIndex(_) + "]"
        or
        this.isUnknownArrayElement(kind) and
        result = kind.getToken() + "[?]"
      )
      or
      exists(MapKind kind |
        this.isMapKey(kind) and
        result = kind.getKeyToken()
        or
        result = kind.getValueToken() + "[" + this.asMapValueWithKnownKey(kind) + "]"
        or
        this.isUnknownMapValue(kind) and
        result = kind.getValueToken() + "[?]"
      )
      or
      result = this.asLanguageContent().toString()
    }
  }

  signature class LanguageContentSetSig {
    Content getAReadContent();

    Content getAStoreContent();

    predicate hasMadToken(string head, string operand);

    string toString();

    Location getLocation();
  }

  module Make<LanguageContentSetSig LanguageContentSet> {
    private newtype TContentSet =
      TSingleton(TContent content) or
      TArrayElementKnownIndex(ArrayKind kind, int index) { index = [0 .. getMaxPreciseIndex(kind)] } or
      TArrayElementLowerBound(ArrayKind kind, int bound) { bound = [0 .. getMaxPreciseIndex(kind)] } or
      TMapValueKnownKey(MapKind kind, MapKey contant) or
      TMapValueAny(MapKind kind) or
      TLanguageContentSet(LanguageContentSet contents)

    class ContentSet extends TContentSet {
      Content asSingleton() { this = TSingleton(result) }

      int asArrayElementLowerBound(ArrayKind kind) { this = TArrayElementLowerBound(kind, result) }

      int asArrayElementKnownIndex(ArrayKind kind) { this = TArrayElementKnownIndex(kind, result) }

      predicate isAnyArrayElement(ArrayKind kind) { this.asArrayElementLowerBound(kind) = 0 }

      predicate isAnyMapValue(MapKind kind) { this = TMapValueAny(kind) }

      MapKey asMapValueWithKnownKey(MapKind kind) { this = TMapValueKnownKey(kind, result) }

      LanguageContentSet asLanguageContentSet() { this = TLanguageContentSet(result) }

      string toString() {
        result = this.asSingleton().toString()
        or
        exists(ArrayKind kind |
          result = kind.getToken() + "[" + this.asArrayElementLowerBound(kind) + "..]"
          or
          result = kind.getToken() + "[" + this.asArrayElementKnownIndex(kind) + "]"
          or
          this.isAnyArrayElement(kind) and
          result = kind.getToken()
        )
        or
        exists(MapKind kind |
          this.isAnyMapValue(kind) and
          result = kind.getValueToken()
        )
        or
        result = this.asLanguageContentSet().toString()
      }

      Location getLocation() { result = this.asLanguageContentSet().getLocation() }

      Content getAReadContent() {
        result = this.asSingleton()
        or
        exists(ArrayKind kind |
          this.asArrayElementLowerBound(kind) <= result.asArrayIndex(kind)
          or
          this.asArrayElementKnownIndex(kind) = result.asArrayIndex(kind)
          or
          this.isAnyArrayElement(kind) and
          exists(result.asArrayIndex(kind))
          or
          (
            exists(this.asArrayElementKnownIndex(kind)) or
            exists(this.asArrayElementLowerBound(kind)) or
            this.isAnyArrayElement(kind)
          ) and
          result.isUnknownArrayElement(kind)
        )
        or
        exists(MapKind kind |
          this.isAnyMapValue(kind) and
          (
            exists(result.asMapValueWithKnownKey(kind))
            or
            result.isUnknownMapValue(kind)
          )
        )
        or
        result = this.asLanguageContentSet().getAReadContent()
      }

      Content getAStoreContent() {
        result = this.asSingleton()
        or
        exists(ArrayKind kind |
          result.asArrayIndex(kind) = this.asArrayElementKnownIndex(kind)
          or
          exists(this.asArrayElementLowerBound(kind)) and
          result.isUnknownArrayElement(kind)
          or
          this.isAnyArrayElement(kind) and
          result.isUnknownArrayElement(kind)
        )
        or
        exists(MapKind kind |
          this.isAnyMapValue(kind) and
          result.isUnknownMapValue(kind)
        )
        or
        result = this.asLanguageContentSet().getAStoreContent()
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

      ContentSet read() { this = TRead(result) }

      ContentSet store() { this = TStore(result) }

      ContentSet withContent() { this = TWithContent(result) }

      ContentSet withoutContent() { this = TWithoutContent(result) }

      string toString() {
        this.value() and result = "value"
        or
        this.taint() and result = "taint"
        or
        result = "read(" + this.read().toString() + ")"
        or
        result = "store(" + this.store().toString() + ")"
        or
        result = "withContent(" + this.withContent().toString() + ")"
        or
        result = "withoutContent(" + this.withoutContent().toString() + ")"
      }
    }

    signature class ArrayKindSig extends ArrayKind;

    /** Generates a module with accessors for content sets associated with the given array kind. */
    module ArrayContent<ArrayKindSig Kind> {
      // TODO: map too-large indices to a lower bound content set
      private Kind kind() { any() }

      pragma[nomagic]
      private int maxIndex() { result = getMaxPreciseIndex(kind()) }

      /** Any element of the array */
      pragma[nomagic]
      ContentSet anyElement() { result.isAnyArrayElement(kind()) }

      /** Read from a index or higher. Using this in a store will result in an unknown index. */
      pragma[nomagic]
      ContentSet lowerBound(int index) { result.asArrayElementLowerBound(kind()) = index }

      pragma[nomagic]
      private ContentSet maxLowerBound() { result = lowerBound(maxIndex()) }

      pragma[nomagic]
      private ContentSet knownIndex(int index) { result.asArrayElementKnownIndex(kind()) = index }

      /**
       * Read or store to a specific index.
       *
       * Reading from this content set will also observe values that were originally stored at an unknown index.
       *
       * Has no result for negative indices. Always has a result for non-negative indices.
       * Indices above a certain threshold will be associated with a less precise content set.
       */
      bindingset[index]
      ContentSet element(int index) {
        result = knownIndex(index)
        or
        // If the index is larger than we can track, use the greatest lower bound instead.
        index > maxIndex() and
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
          this.asSingleton().isUnknownArrayElement(kind())
        }

        /** Increase the index by the given value, if it is a known index. */
        bindingset[index]
        ContentSet shiftUpBy(int index) {
          result = element(this.asSingleton().asArrayIndex(kind()) + index)
          or
          this.asSingleton().isUnknownArrayElement(kind()) and result = this
        }
      }
    }

    signature class MapKindSig extends MapKind;

    /** Generates a module with accessors for content sets associated with the given map kind. */
    module MapContent<MapKindSig Kind> {
      private Kind kind() { any() }

      /** One of the keys in a key-value pair stored in a map. */
      pragma[nomagic]
      ContentSet key() { result.asSingleton().isMapKey(kind()) }

      /** One of the values from a key-value pair stored in a map. */
      pragma[nomagic]
      ContentSet value() { result.isAnyMapValue(kind()) }

      pragma[nomagic]
      private ContentSet valueAtExact(MapKey key) {
        result.asSingleton().asMapValueWithKnownKey(kind()) = key
      }

      /**
       * The value associated with `key` in map.
       *
       * If `key` is not one of the keys that are tracked precisely, this will return
       * the same as `value()`.
       */
      bindingset[key]
      ContentSet valueAt(MapKey key) {
        result = valueAtExact(key)
        or
        not exists(valueAtExact(key)) and
        result = value()
      }
    }

    class DataFlowNode instanceof AstNode {
      bindingset[this]
      DataFlowNode() { any() }

      string toString() { result = super.toString() }

      Location getLocation() { result = super.getLocation() }
    }

    class Stage1Step extends Unit {
      predicate step(DataFlowNode node1, DataFlowNode node2) { none() }
    }
  }
}
