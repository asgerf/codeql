private import All
private import Contents
private import DataFlowBuilder

ContentSet getContentSetFromKey(AstNode key) {
  result = property(key.(PropertyIdentifier).getValue()) or
  result = property(key.(ShorthandPropertyIdentifier).getValue()) or
  result = property(key.(ShorthandPropertyIdentifierPattern).getValue()) or
  result = property(getStringValueFromNode(key)) or
  result = ArrayContent::elementAt(getIntValueFromNode(key))
}

predicate dataflowStep(Node1 node1, Step step, Node2 node2) {
  //
  // Flow out of expressions
  //
  exists(Array array, int i |
    node1 = array.getChild(i) and
    node2 = array
  |
    if i >= array.getFirstSpreadIndex()
    then step.store(ArrayContent::anyElement())
    else step.store(ArrayContent::elementAt(i))
  )
  or
  // For an array spread '...x' we first read the contents of 'x' into '...x' before storing that back into the array
  // The store happened above as part of the rule for array literals
  exists(ArraySpreadElement spread |
    node1 = spread.getChild() and
    node2 = spread
  |
    step.read(ArrayContent::anyElement())
    or
    step.taint() // In case the entire input array is tainted
  )
  or
  exists(Object object |
    // For `{ k: v }`, store 'v' into the 'k' property of the object
    exists(PairLike pair | object.getChild(_) = pair |
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
  exists(PropAccess prop |
    not isInPureLValuePosition(prop) and
    node1 = prop.getObject() and
    node2 = prop
  |
    step.read(getContentSetFromKey(prop.getPropertyNameNode()))
    or
    not exists(getContentSetFromKey(prop.getPropertyNameNode())) and
    prop instanceof SubscriptExpression and
    step.read(ArrayContent::anyElement())
    or
    step.taint()
  )
  or
  exists(BinaryExpressionLike binary |
    binary.getOperator() = "+" and
    node1 = [binary.getLeft(), binary.getRight()] and
    node2 = binary and
    step.taint()
  )
  or
  exists(TemplateString str |
    node1 = str.getChild(_) and
    node2 = str and
    step.taint()
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
    step.read(ArrayContent::anyElement())
  )
  or
  exists(ImportStatement stmt, AstNode child |
    node1 = stmt.getImportedModuleNode() and
    child = stmt.getASpecifier()
  |
    exists(ImportSpecifier spec |
      spec = child and
      step.read(getContentSetFromKey(spec.getName())) and
      node2 = getLValueNode(spec.getLocalName())
    )
    or
    step.value() and
    node2 = getLValueNode(child.(NamespaceImport).getChild())
    or
    step.value() and
    node2 = getLValueNode(child.(Identifier)) // default import
  )
  or
  exists(FunctionDeclaration stmt |
    node1 = stmt and
    step.value() and
    node2 = getLValueNode(stmt.getName())
  )
  or
  exists(ClassLike cls |
    node1 = cls and
    step.value() and
    node2 = getLValueNode(cls.getNameNode())
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
    step.store(ArrayContent::anyElement())
  )
  or
  // Flow into `[ x ]` results in an array-element read into the nested lvalue `x`
  exists(ArrayPattern pattern, int n |
    node1 = getLValueNode(pattern) and
    step.read(ArrayContent::elementAt(n)) and
    node2 = getLValueNode(pattern.getChild(n))
  )
  or
  // Flow into `[ x, ...rest ]` results in a read into `...rest` followed by a store into the nested lvalue `rest`.
  exists(ArrayRestPattern rest |
    node1 = getLValueNode(rest.getArrayPattern()) and
    step.read(ArrayContent::anyElement()) and
    node2 = rest
    or
    node1 = rest and
    step.store(ArrayContent::anyElement()) and
    node2 = getLValueNode(rest.getChild())
  )
  or
  exists(ObjectPattern object, PairPatternLike pair |
    pair = object.getChild(_) and
    node1 = getLValueNode(object) and
    step.read(getContentSetFromKey(pair.getKey())) and
    node2 = getLValueNode(pair.getValue())
  )
  or
  // Flow into `{ ...rest }` results in a direct flow edge to the nested lvalue `rest`.
  // (In the future we may consider using clearsContent here to filter out `x` in `{...rest, x}`)
  exists(ObjectRestPattern rest |
    node1 = getLValueNode(rest.getObjectPattern()) and
    (
      step.withContent(anyProperty())
      or
      step.taint()
    ) and
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
  or
  // Arguments and return value of a call
  exists(CallExpression call |
    exists(int n |
      node1 = call.getArgument(n) and
      not node1 instanceof SpreadElement and
      node2 = getArgumentObjectNode(call)
    |
      if n >= call.getFirstSpreadIndex()
      then step.store(ArrayContent::anyElement())
      else step.store(ArrayContent::elementAt(n))
    )
    or
    exists(int n |
      node1 = call.getArgument(n).(SpreadElement).getChild() and
      node2 = getArgumentObjectNode(call)
    |
      if n = call.getFirstSpreadIndex()
      then step.shiftArrayContentsBy(ArrayContent::kind(), n)
      else step.resetArrayContents(ArrayContent::kind())
    )
    or
    node1 = call.getFunction().(PropAccess).getObject() and
    node2 = getArgumentObjectNode(call) and
    step.store(Contents::thisArgument())
    or
    node1 = call.getFunction() and
    node2 = getArgumentObjectNode(call) and
    step.store(Contents::functionSelfReference())
    or
    node1 = getReturnValueNode(call) and
    step.value() and
    node2 = call
  )
  or
  // Parameters and return value of a function
  exists(Callable callable |
    exists(int n |
      node1 = getParameterObjectNode(callable) and
      node2 = callable.getParameter(n) and
      if node2 instanceof RestParameter
      then step.shiftArrayContentsBy(ArrayContent::kind(), -n)
      else step.read(ArrayContent::elementAt(n))
    )
    or
    node1 = getParameterObjectNode(callable) and
    step.read(Contents::thisArgument()) and
    node2 = callable.getThisParameter()
    or
    not callable instanceof FunctionDeclaration and // for FunctionDeclarations, the variable belongs to the outer scope
    node1 = getParameterObjectNode(callable) and
    step.read(Contents::functionSelfReference()) and
    node2 = getLValueNode(callable.getNameNode())
    or
    node1 = callable.getAReturnedExpr() and
    node2 = getReturnValueNode(callable) and
    if callable.isAsync() then step.store(Contents::promiseValue()) else step.value()
  )
  or
  exists(Parameter param |
    node1 = param and
    step.value() and
    if param instanceof RestParameter
    then node2 = getLValueNode(param.(RestParameter).getChild())
    else node2 = getLValueNode(param)
  )
}
