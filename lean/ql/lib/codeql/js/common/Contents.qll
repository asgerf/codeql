private import javascript

newtype TContent =
  TProperty(string name) { name = any(PropertyIdentifier e).getValue() } or
  TUnknownArrayElement()

class Content extends TContent {
  string asPropertyName() { this = TProperty(result) }

  int asArrayIndex() { result = this.asPropertyName().toInt() }

  predicate isUnknownArrayElement() { this = TUnknownArrayElement() }

  string toString() { result = this.asPropertyName() }
}

newtype TContentSet =
  TSingleton(TContent content) or
  TArrayElementKnown(int n) { n in [0 .. 20] } or
  TAnyArrayElement() or
  TAnyProperty()

class ContentSet extends TContentSet {
  Content asSingleton() { this = TSingleton(result) }

  string asPropertyName() { result = this.asSingleton().asPropertyName() }

  int asArrayElementKnown() { this = TArrayElementKnown(result) }

  predicate isAnyArrayElement() { this = TAnyArrayElement() }

  string toString() { result = this.asSingleton().toString() }

  Content getAReadContent() {
    result = this.asSingleton()
    or
    exists(int n | n = this.asArrayElementKnown() |
      result.asArrayIndex() = n
      or
      result.isUnknownArrayElement()
    )
    or
    this.isAnyArrayElement() and
    (
      exists(result.asArrayIndex())
      or
      result.isUnknownArrayElement()
    )
    or
    this = TAnyProperty() and
    any()
  }

  Content getAStoreContent() {
    result = this.asSingleton()
    or
    result.asArrayIndex() = this.asArrayElementKnown()
    or
    this.isAnyArrayElement() and
    result.isUnknownArrayElement()
  }
}

module ContentSet {
  bindingset[n]
  ContentSet arrayElementKnown(int n) {
    result = TArrayElementKnown(n)
    or
    not exists(TArrayElementKnown(n)) and
    result = TAnyArrayElement()
  }
}
