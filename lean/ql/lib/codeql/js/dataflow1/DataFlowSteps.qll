private import codeql.js.common.All
private import LanguageDataflowJS
private import Contents

predicate arrayElement = Array::elementAt/1;

predicate anyArrayElement = Array::anyElement/0;

ContentSet getContentSetFromKey(AstNode key) {
  result = property(key.(PropertyIdentifier).getValue()) or
  result = property(key.(ShorthandPropertyIdentifier).getValue()) or
  result = property(key.(ShorthandPropertyIdentifierPattern).getValue()) or
  result = property(getStringValueFromNode(key)) or
  result = arrayElement(getIntValueFromNode(key))
}

private predicate objectPatternKeyValue(ObjectPattern pattern, AstNode key, AstNode value) {
  exists(PairPattern pair |
    pattern.getChild(_) = pair and
    key = pair.getKey() and
    value = getLValueNode(pair.getValue())
  )
  or
  exists(ShorthandPropertyIdentifierPattern shorthand |
    pattern.getChild(_) = shorthand and
    key = shorthand and
    value = getLValueNode(shorthand)
  )
}

predicate dataflowStep(DataFlowBuilder node1, Step step, DataFlowBuilder node2) {
  //
  // Flow out of expressions
  //
  exists(Array array, int i |
    node1 = array.getChild(i) and
    node2 = array
  |
    if i >= array.getFirstSpreadIndex()
    then step.store(anyArrayElement())
    else step.store(arrayElement(i))
  )
  or
  // For an array spread '...x' we first read the contents of 'x' into '...x' before storing that back into the array
  // The store happened above as part of the rule for array literals
  exists(ArraySpreadElement spread |
    node1 = spread.getChild() and
    node2 = spread
  |
    step.read(Array::anyElement()) // Will be stored back into the created array under different indices
    or
    step.taint() // In case the entire input array is tainted
  )
  or
  exists(Object object |
    // For `{ k: v }`, store 'v' into the 'k' property of the object
    exists(Pair pair | object.getChild(_) = pair |
      node1 = pair.getValue() and
      step.store(getContentSetFromKey(pair.getKey())) and
      node2 = object
    )
    or
    exists(MethodDefinition method | object.getChild(_) = method |
      node1 = method and // the MethodDefinition is the representative for the function expression being stored
      step.store(getContentSetFromKey(method.getName())) and
      node2 = object
    )
  )
  or
  exists(ObjectSpreadElement spread |
    // Step from 'x' to '{ ...x }', preserving only property names
    node1 = spread.getChild() and
    (
      step.withContent(anyProperty())
      or
      step.taint() // handle the case where the entire object was tainted (and thus is not in a content)
    ) and
    node2 = spread.getObject()
  )
  or
  //
  //  Assignments into L-values
  //
  exists(VariableDeclarator decl |
    node1 = decl.getValue() and
    step.value() and
    node2 = getLValueNode(decl.getName())
  )
  or
  exists(AssignmentExpression asn |
    node1 = asn.getRight() and
    step.value() and
    node2 = [asn, getLValueNode(asn.getLeft())]
  )
  or
  exists(AugmentedAssignmentExpression asn |
    node1 = asn.getBinaryOperatorNode() and
    step.value() and
    node2 = [asn, getLValueNode(asn.getLeft())]
  )
  or
  exists(ForInStatement stmt |
    node1 = stmt.getRight() and
    node2 = getLValueNode(stmt.getLeft())
  |
    stmt.getOperator() = "in" and
    step.taint()
    or
    stmt.getOperator() = "of" and
    step.read(anyArrayElement())
  )
  or
  exists(ImportStatement stmt, AstNode child |
    node1 = stmt.getImportedModuleNode() and
    child = stmt.getASpecifier()
  |
    exists(ImportSpecifier spec |
      spec = child and
      step.read(getContentSetFromKey(spec.getName()))
    |
      node2 = getLValueNode(spec.getAlias())
      or
      not exists(spec.getAlias()) and
      node2 = getLValueNode(spec.getName())
    )
    or
    step.value() and
    (
      node2 = getLValueNode(child.(NamespaceImport).getChild())
      or
      node2 = getLValueNode(child.(Identifier)) // default import
    )
  )
  or
  //
  //   Effects of L-values other than local variables
  //
  // Flow into a member expression `e.f` results into store into `e`
  exists(PropAccess expr, AstNode key |
    node1 = getLValueNode(expr) and
    node2 = getPostUpdate(expr.getObject()) and
    key = expr.getPropertyNameNode()
  |
    step.store(getContentSetFromKey(key))
    or
    not exists(getContentSetFromKey(key)) and
    isLikelyArrayAccess(expr) and
    step.store(anyArrayElement())
  )
  or
  // Flow into `[ x, ...rest ]` results in a read into `...rest` followed by a store into the nested lvalue `rest`.
  // This is the store part.
  exists(ArrayRestPattern rest |
    node1 = rest and
    step.store(anyArrayElement()) and
    node2 = getLValueNode(rest.getChild())
  )
  or
  // Flow into `{ p: v }` results in a read of `p` into the nested lvalue `v`
  exists(AstNode key | objectPatternKeyValue(node1, key, node2) |
    step.read(getContentSetFromKey(key))
    or
    not exists(getContentSetFromKey(key)) and
    step.read(anyArrayElement())
  )
  or
  // Flow into `[ x ]` results in an array-element read into the nested lvalue `x`
  exists(ArrayPattern pattern, int n |
    node1 = pattern and
    step.read(arrayElement(n)) and
    node2 = getLValueNode(pattern.getChild(n))
  )
  or
  // Flow into `[ x, ...rest ]` results in a read into `...rest` followed by a store into the nested lvalue `rest`.
  // This is the read part.
  exists(ArrayRestPattern rest |
    node1 = rest.getArrayPattern() and
    step.read(anyArrayElement()) and
    node2 = rest
  )
  or
  // Flow into `{ ...rest }` results in a direct flow edge to the nested lvalue `rest`.
  // (In the future we may consider using clearsContent here to filter out `x` in `{...rest, x}`)
  exists(ObjectRestPattern rest |
    node1 = rest.getObjectPattern() and
    step.value() and
    node2 = getLValueNode(rest.getChild())
  )
  or
  step.value() and
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

import Make3<dataflowStep/3>
