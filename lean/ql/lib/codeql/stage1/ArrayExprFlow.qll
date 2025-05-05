private import javascript
private import Stage1

private int getFirstSpreadElementIndex(Array array) {
  result = min(int i | array.getChild(i) instanceof SpreadElement)
}

/**
 * Flow rules for array literals and their spread elements.
 */
class ArrayExprFlow extends Stage1 {
  override predicate storeStep(Node node1, ContentSet contents, Node node2) {
    exists(Array array, int i |
      node1 = array.getChild(i) and
      node2 = array
    |
      if i >= getFirstSpreadElementIndex(array)
      then contents.isAnyArrayElement()
      else contents = ContentSet::arrayElementKnown(i)
    )
  }

  override predicate readStep(Node node1, ContentSet contents, Node node2) {
    exists(ArraySpreadElement spread |
      node1 = spread.getChild() and
      contents.isAnyArrayElement() and
      node2 = spread // will be stored back into the created array under different indices
    )
  }

  override predicate taintStep(Node node1, Node node2) {
    // Alternative to the read step above, in case entire input array is tainted
    exists(ArraySpreadElement spread |
      node1 = spread.getChild() and
      node2 = spread
    )
  }
}
