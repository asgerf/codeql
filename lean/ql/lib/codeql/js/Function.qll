private import javascript

final class Function = FunctionImpl;

final class FunctionOrProgram = FunctionOrProgramImpl;

abstract private class FunctionOrProgramImpl extends AstNode { }

private class ProgramAsImpl extends FunctionOrProgramImpl instanceof Program { }

abstract private class FunctionImpl extends FunctionOrProgramImpl {
  abstract Node getParameter(int i);

  int getNumParameter() { result = count(int i | exists(this.getParameter(i))) }

  abstract Node getBody();

  Node getNameNode() { none() }

  string getName() {
    result = inferNameFromNode(this.getNameNode())
    or
    not exists(inferNameFromNode(this.getNameNode())) and
    result = inferNameFromContext(this)
  }

  Expression getAReturnedExpr() {
    result = this.getBody() // arrow function with expression body
    or
    exists(ReturnStatement ret |
      getEnclosingFunctionOrProgram(ret) = this and
      result = ret.getChild()
    )
  }

  override string toString() {
    result = this.getName()
    or
    not exists(this.getName()) and result = "anonymous function"
  }
}

/**
 * Gets the nearest enclosing function or program, possibly `node` itself.
 */
pragma[nomagic]
FunctionOrProgram getEnclosingFunctionOrProgram(Node node) {
  result = node
  or
  not node instanceof Function and
  not node instanceof Program and
  result = getEnclosingFunctionOrProgram(node.getParent())
}

private class ArrowFunctionAsImpl extends FunctionImpl instanceof ArrowFunction {
  override Node getParameter(int i) {
    // `(x) => { ... }`
    result = super.getParameters().getChild(i)
    or
    // `x => {..}` (no parenthesis around parameter)
    result = super.getParameter() and i = 0
  }

  override Node getBody() { result = ArrowFunction.super.getBody() }
}

private class FunctionDeclarationAsImpl extends FunctionImpl instanceof FunctionDeclaration {
  override Node getParameter(int i) { result = super.getParameters().getChild(i) }

  override Node getNameNode() { result = FunctionDeclaration.super.getName() }

  override Node getBody() { result = FunctionDeclaration.super.getBody() }
}

private class FunctionExpressionAsImpl extends FunctionImpl instanceof FunctionExpression {
  override Node getParameter(int i) { result = super.getParameters().getChild(i) }

  override Node getNameNode() { result = FunctionExpression.super.getName() }

  override Node getBody() { result = FunctionExpression.super.getBody() }
}

private class GeneratorFunctionAsImpl extends FunctionImpl instanceof GeneratorFunction {
  override Node getParameter(int i) { result = super.getParameters().getChild(i) }

  override Node getNameNode() { result = GeneratorFunction.super.getName() }

  override Node getBody() { result = GeneratorFunction.super.getBody() }
}

private class GeneratorFunctionDeclarationAsImpl extends FunctionImpl instanceof GeneratorFunctionDeclaration
{
  override Node getParameter(int i) { result = super.getParameters().getChild(i) }

  override Node getNameNode() { result = GeneratorFunctionDeclaration.super.getName() }

  override Node getBody() { result = GeneratorFunctionDeclaration.super.getBody() }
}

private class MethodDefinitionAsImpl extends FunctionImpl instanceof MethodDefinition {
  override Node getParameter(int i) { result = super.getParameters().getChild(i) }

  override Node getNameNode() { result = MethodDefinition.super.getName() }

  override Node getBody() { result = MethodDefinition.super.getBody() }
}
