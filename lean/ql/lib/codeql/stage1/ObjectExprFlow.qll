private import javascript
private import Stage1

/**
 * Flow rules for object literals and their spread elements.
 */
class ObjectExprFlow extends Stage1 {
  override predicate expectsContent(Node node, ContentSet contents) {
    // Ensure only properties get copied via `{...spread}`
    node instanceof ObjectSpreadElement and
    contents = TAnyProperty()
  }

  override predicate valueStep(Node node1, Node node2) {
    exists(ObjectSpreadElement spread |
      node1 = spread.getChild() and
      node2 = spread
      or
      node1 = spread and
      node2 = spread.getObject()
    )
  }

  override predicate taintStep(Node node1, Node node2) {
    // If the spread value is entirely tainted, skip over the expectsContent node to avoid blocking flow
    exists(ObjectSpreadElement spread |
      node1 = spread.getChild() and
      node2 = spread.getObject()
    )
  }

  override predicate storeStep(Node node1, ContentSet contents, Node node2) {
    exists(Object object | node2 = object |
      exists(Pair pair | object.getChild(_) = pair |
        node1 = pair.getValue() and
        contents = getContentSetFromKey(pair.getKey())
      )
      or
      exists(MethodDefinition method | object.getChild(_) = method |
        node1 = method and // the MethodDefinition is the representative for the function expression being stored
        contents = getContentSetFromKey(method.getName())
      )
    )
  }
}
