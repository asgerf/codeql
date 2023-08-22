private import javascript

Function getLambdaFromVariable(LocalVariable variable) {
  result.getVariable() = variable
  or
  result = variable.getAnAssignedExpr()
  or
  exists(ClassDeclStmt cls |
    result = cls.getConstructor().getBody() and
    variable = cls.getVariable()
  )
}

predicate captures(Function fun, LocalVariable variable) {
  (
    variable.getAnAccess().getContainer().getFunctionBoundary() = fun
    or
    exists(Function inner |
      captures(inner, variable) and
      fun = inner.getEnclosingContainer().getFunctionBoundary()
    )
    or
    // if capturing another function, include the captures of that function
    exists(LocalVariable otherLambdaVar |
      captures(fun, otherLambdaVar) and
      captures(getLambdaFromVariable(otherLambdaVar), variable)
    )
  ) and
  not variable.getDeclaringContainer() = fun
}
