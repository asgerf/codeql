private import codeql.js.common.All
private import codeql.util.Unit
private import codeql.util.Void
private import codeql.shared.LanguageDataflow::LanguageDataFlow<Location, LanguageBase, LanguageCommon> as DataFlowBuilder
private import DataFlowBuilder

module LanguageDataFlowInput implements LanguageDataFlowSig {
  import codeql.js.common.Variables

  private newtype TConstant = TInteger(int x) { x = [0 .. 20] }

  class Constant extends TConstant {
    int asArrayIndex() { this = TInteger(result) }

    string getAsOperand() { result = this.asArrayIndex().toString() }

    string toString() { result = this.getAsOperand() }
  }

  private newtype TIndexedContainerKind =
    TArray() or
    TMap()

  class IndexedContainerKind extends TIndexedContainerKind {
    string toString() { none() }

    /** Holds if data flowing into the keys themselves should be tracked. For array-like containers this should be `none()`. */
    predicate trackFlowIntoKeys() { none() }

    /** Gets the MaD token to associate with keys in this map-like container. Should have no result for array-like containers. */
    string getKeyToken() { none() }

    /** Gets the MaD token to associate with values in this container (i.e. map values or array elements). */
    string getValueToken() { none() }

    /**
     * Holds if values that are associated with `key` should be tracked precisely.
     *
     * For array-like containers, this should hold for non-negative integers up to a certain size.
     *
     * For map-like containers, this should hold for all keys that are likely worth tracking.
     */
    predicate trackValuesAssociatedWithKey(Constant key) { none() }
  }

  additional class ArrayContainerKind extends IndexedContainerKind, TArray {
    override string toString() { result = "Array" }

    override string getValueToken() { result = "ArrayElement" }
  }

  additional class MapContainerKind extends IndexedContainerKind, TMap {
    override string toString() { result = "Map" }

    override string getKeyToken() { result = "MapKey" }

    override string getValueToken() { result = "MapValue" }

    override predicate trackValuesAssociatedWithKey(Constant key) {
      none() // TODO
    }
  }

  private newtype TLanguageContent =
    TPropertyName(string name) { name = any(PropertyIdentifier id).getValue() }

  class LanguageContent extends TLanguageContent {
    string asPropertyName() { this = TPropertyName(result) }

    predicate hasMadToken(string head, string operand) {
      head = "Member" and
      operand = this.asPropertyName()
    }

    string toString() { result = this.asPropertyName() }

    Location getLocation() { none() }
  }
}

private import LanguageDataFlowInput

private module Dataflow1 = Make1<LanguageDataFlowInput>;

import Dataflow1

private newtype TLanguageContentSet = TAnyProperty()

class LanguageContentSet extends TLanguageContentSet {
  Content getAReadContent() {
    this instanceof TAnyProperty and
    (
      exists(result.asLanguageContent().asPropertyName())
      or
      exists(result.asContainerSlot(any(ArrayContainerKind a)))
    )
  }

  Content getAStoreContent() { none() }

  predicate hasMadToken(string head, string operand) { none() }

  Location getLocation() { none() }

  string toString() { this = TAnyProperty() and result = "anyProperty" }
}

ContentSet anyProperty() { result.asLanguageContentSet() = TAnyProperty() }

private module Dataflow2 = Make2<LanguageContentSet>;

import Dataflow2

module Contents {
  module Array = ArrayContentAccessor<ArrayContainerKind>;

  module Map = MapContentAccessor<ArrayContainerKind>;

  ContentSet property(string name) {
    result.asSingleton().asLanguageContent().asPropertyName() = name
  }
}
