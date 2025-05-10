private import All

/**
 * Steps generated from flow into LValue nodes.
 */
class LValueNode extends Stage1 {
  override predicate storeStep(Node node1, ContentSet contents, Node node2) {
    // Flow into a member expression `e.f` results into store into `e`
    exists(PropAccess expr, Node key |
      node1 = getLValueNode(expr) and
      node2 = getPostUpdate(expr.getObject()) and
      key = expr.getPropertyNameNode()
    |
      contents = getContentSetFromKey(key)
      or
      not exists(getContentSetFromKey(key)) and
      isLikelyArrayAccess(expr) and
      contents.asSingleton().isUnknownArrayElement()
    )
    or
    // Flow into `[ x, ...rest ]` results in a read into `...rest` followed by a store into the nested lvalue `rest`.
    // This is the store part.
    exists(ArrayRestPattern rest |
      node1 = rest and
      contents.asSingleton().isUnknownArrayElement() and
      node2 = getLValueNode(rest.getChild())
    )
  }

  override predicate readStep(Node node1, ContentSet contents, Node node2) {
    // Flow into `{ p: v }` results in a read of `p` into the nested lvalue `v`
    exists(ObjectPattern pattern, PairPattern pair, Node key |
      node1 = pattern and
      pattern.getChild(_) = pair and
      node2 = getLValueNode(pair.getValue()) and
      key = pair.getKey()
    |
      contents = getContentSetFromKey(key)
      or
      not exists(getContentSetFromKey(key)) and
      contents.isAnyArrayElement()
    )
    or
    // Flow into `[ x ]` results in an array-element read into the nested lvalue `x`
    exists(ArrayPattern pattern, int n |
      node1 = pattern and
      contents = ContentSet::arrayElementKnown(n) and
      node2 = getLValueNode(pattern.getChild(n)) and
      not node2 instanceof RestPattern
    )
    or
    // Flow into `[ x, ...rest ]` results in a read into `...rest` followed by a store into the nested lvalue `rest`.
    // This is the read part.
    exists(ArrayRestPattern rest |
      node1 = rest.getArrayPattern() and
      contents.isAnyArrayElement() and
      node2 = rest
    )
  }

  override predicate valueStep(Node node1, Node node2) {
    // Flow into `{ ...rest }` results in a direct flow edge to the nested lvalue `rest`.
    // (In the future we may consider using clearsContent here to filter out `x` in `{...rest, x}`)
    exists(ObjectRestPattern rest |
      node1 = rest.getObjectPattern() and
      node2 = getLValueNode(rest.getChild())
    )
    or
    exists(AssignmentPattern assign |
      // Example:
      //
      //   let {x: y = 3} = z
      //
      // This is equivalent to:
      //
      //   let y = z.x ?? 3
      //
      // We generate the same steps as for the '??' operator
      node1 = getLValueNode(assign) and
      node2 = getLValueNode(assign.getLeft())
      or
      node1 = assign.getRight() and
      node2 = getLValueNode(assign.getLeft())
    )
  }
}
