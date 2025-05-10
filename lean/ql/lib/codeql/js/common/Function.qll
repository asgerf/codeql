private import All

final class Function = FunctionImpl;

abstract private class FunctionImpl extends AstNode {
  /** Gets the `i`th parameter of this function. */
  final Parameter getParameter(int i) { result = this.getRawParameter(i) }

  abstract AstNode getRawParameter(int i);

  int getNumParameter() { result = count(int i | exists(this.getRawParameter(i))) }

  abstract AstNode getBody();

  AstNode getNameNode() { none() }

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
      getCfgScope(ret) = this and
      result = ret.getChild()
    )
  }

  override string toString() {
    result = this.getName()
    or
    not exists(this.getName()) and result = "anonymous function"
  }
}

private class ArrowFunctionAsImpl extends FunctionImpl instanceof ArrowFunction {
  override AstNode getRawParameter(int i) {
    // `(x) => { ... }`
    result = super.getParameters().getChild(i)
    or
    // `x => {..}` (no parenthesis around parameter)
    result = super.getParameter() and i = 0
  }

  override AstNode getBody() { result = ArrowFunction.super.getBody() }
}

private class FunctionDeclarationAsImpl extends FunctionImpl instanceof FunctionDeclaration {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = FunctionDeclaration.super.getName() }

  override AstNode getBody() { result = FunctionDeclaration.super.getBody() }
}

private class FunctionExpressionAsImpl extends FunctionImpl instanceof FunctionExpression {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = FunctionExpression.super.getName() }

  override AstNode getBody() { result = FunctionExpression.super.getBody() }
}

private class GeneratorFunctionAsImpl extends FunctionImpl instanceof GeneratorFunction {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = GeneratorFunction.super.getName() }

  override AstNode getBody() { result = GeneratorFunction.super.getBody() }
}

private class GeneratorFunctionDeclarationAsImpl extends FunctionImpl instanceof GeneratorFunctionDeclaration
{
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = GeneratorFunctionDeclaration.super.getName() }

  override AstNode getBody() { result = GeneratorFunctionDeclaration.super.getBody() }
}

private class MethodDefinitionAsImpl extends FunctionImpl instanceof MethodDefinition {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = MethodDefinition.super.getName() }

  override AstNode getBody() { result = MethodDefinition.super.getBody() }
}

class Parameter extends AstNode {
  private Function function;
  private int index;

  Parameter() { this = function.getRawParameter(index) }

  Function getFunction() { result = function }

  int getIndex() { result = index }

  Expression getDefaultValue() { result = this.(AssignmentPattern).getRight() }
}
