private import All
private import codeql.util.Unit
private import codeql.util.Void
private import codeql.shared.LanguageDataflow::LanguageDataFlow<Location, LanguageBase, LanguageCommon> as LanguageDataFlow
private import LanguageDataFlow
private import DataFlowSteps

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
    string toString() {
      this = TArray() and result = "Array"
      or
      this = TMap() and result = "Map"
    }

    predicate trackFlowIntoKeys() { this = TMap() }

    string getKeyToken() { this = TMap() and result = "MapKey" }

    string getValueToken() {
      this = TArray() and result = "ArrayElement"
      or
      this = TMap() and result = "MapValue"
    }

    predicate trackValuesAssociatedWithKey(Constant key) {
      this = TMap() and exists(key)
      or
      this = TArray() and key.asArrayIndex() = [0 .. 20]
    }
  }

  additional class ArrayContainerKind extends IndexedContainerKind, TArray { }

  additional class MapContainerKind extends IndexedContainerKind, TMap { }

  private newtype TLanguageContent =
    TPropertyName(string name) { name = any(PropertyIdentifier id).getValue() } or
    TThisArgument() or
    TFunctionSelfReference() or
    TPromiseValue() or
    TPromiseError()

  class LanguageContent extends TLanguageContent {
    string asPropertyName() { this = TPropertyName(result) }

    predicate isPromiseValue() { this = TPromiseValue() }

    predicate isPromiseError() { this = TPromiseError() }

    predicate hasMadToken(string head, string operand) {
      head = "Member" and
      operand = this.asPropertyName()
      or
      this = TThisArgument() and head = "Argument" and operand = "this"
      or
      this = TFunctionSelfReference() and head = "Argument" and operand = "function"
      or
      this = TPromiseValue() and head = "Awaited" and operand = "value"
      or
      this = TPromiseError() and head = "Awaited" and operand = "error"
    }

    string toString() {
      result = this.asPropertyName()
      or
      this = TThisArgument() and result = "this"
      or
      this = TFunctionSelfReference() and result = "FunctionSelfReference"
      or
      this = TPromiseValue() and result = "Promise.value"
      or
      this = TPromiseError() and result = "Promise.error"
    }

    Location getLocation() { none() }
  }

  private newtype TLanguageContentSet = TAnyProperty()

  additional class LanguageContentSet extends TLanguageContentSet {
    Content getAReadContent() {
      this instanceof TAnyProperty and
      (
        exists(result.asLanguageContent().asPropertyName())
        or
        exists(result.asContainerSlot(any(ArrayContainerKind a)))
      )
    }

    Content getAStoreContent() { none() }

    predicate hasMadToken(string head, string operand) {
      this = TAnyProperty() and head = "AnyMember" and operand = ""
    }

    Location getLocation() { none() }

    string toString() { this = TAnyProperty() and result = "anyProperty" }
  }

  additional module Contents {
    module ArrayContent = ArrayContentAccessor<ArrayContainerKind>;

    module MapContent = MapContentAccessor<MapContainerKind>;

    ContentSet property(string name) {
      result.asSingleton().asLanguageContent().asPropertyName() = name
    }

    ContentSet anyProperty() { result.asLanguageContentSet() = TAnyProperty() }

    ContentSet thisArgument() { result.asSingleton().asLanguageContent() = TThisArgument() }

    Content functionSelfReferenceContent() { result.asLanguageContent() = TFunctionSelfReference() }

    ContentSet functionSelfReference() {
      result.asSingleton().asLanguageContent() = TFunctionSelfReference()
    }

    ContentSet promiseValue() { result.asSingleton().asLanguageContent() = TPromiseValue() }

    ContentSet promiseError() { result.asSingleton().asLanguageContent() = TPromiseError() }
  }

  class ClosureExpr extends Callable {
    predicate hasBody(Callable callable) { callable = this }
  }
}

private import LanguageDataFlowInput

private module Dataflow1 = Make1<LanguageDataFlowInput>;

private import Dataflow1

private module Dataflow2 = Make2<LanguageContentSet, Contents::functionSelfReferenceContent/0>;

private import Dataflow2

private module Dataflow3 = Make3<dataflowStep/3, LanguageCfg>;

class Content = Dataflow1::Content;

class ContentSet = Dataflow2::ContentSet;

module Contents = LanguageDataFlowInput::Contents;

module DataFlowBuilder = Dataflow2::DataFlowBuilder;

module DataFlow = Dataflow3::DataFlowPublic;
