private import All

final class Callable = CallableImpl;

abstract private class CallableImpl extends AstNode {
  /** Gets the `i`th parameter of this function. */
  final Parameter getParameter(int i) { result = this.getRawParameter(i) }

  abstract AstNode getRawParameter(int i);

  int getNumParameter() { result = count(int i | exists(this.getRawParameter(i))) }

  abstract AstNode getBody();

  /**
   * Gets the identifier declared as part of this function, if any.
   */
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
      getEnclosingCallable(ret) = this and
      result = ret.getChild()
    )
  }

  override string toString() {
    result = this.getName()
    or
    not exists(this.getName()) and result = "anonymous function"
  }

  predicate isAsync() {
    exists(Token asyncToken |
      asyncToken.getValue() = "async" and
      asyncToken.getParent() = this
    )
  }

  predicate isGenerator() {
    this instanceof GeneratorFunction or this instanceof GeneratorFunctionDeclaration
  }

  predicate isAsyncGenerator() { this.isAsync() and this.isGenerator() }

  predicate isAsyncOrGenerator() { this.isAsync() or this.isGenerator() }
}

private class ArrowFunctionAsCallable extends CallableImpl instanceof ArrowFunction {
  override AstNode getRawParameter(int i) {
    // `(x) => { ... }`
    result = super.getParameters().getChild(i)
    or
    // `x => {..}` (no parenthesis around parameter)
    result = super.getParameter() and i = 0
  }

  override AstNode getBody() { result = ArrowFunction.super.getBody() }
}

private class FunctionDeclarationAsCallable extends CallableImpl instanceof FunctionDeclaration {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = FunctionDeclaration.super.getName() }

  override AstNode getBody() { result = FunctionDeclaration.super.getBody() }
}

private class FunctionExpressionAsCallable extends CallableImpl instanceof FunctionExpression {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = FunctionExpression.super.getName() }

  override AstNode getBody() { result = FunctionExpression.super.getBody() }
}

private class GeneratorFunctionAsCallable extends CallableImpl instanceof GeneratorFunction {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = GeneratorFunction.super.getName() }

  override AstNode getBody() { result = GeneratorFunction.super.getBody() }
}

private class GeneratorFunctionDeclarationAsCallable extends CallableImpl instanceof GeneratorFunctionDeclaration
{
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = GeneratorFunctionDeclaration.super.getName() }

  override AstNode getBody() { result = GeneratorFunctionDeclaration.super.getBody() }
}

private class MethodDefinitionAsCallable extends CallableImpl instanceof MethodDefinition {
  override AstNode getRawParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = MethodDefinition.super.getName() }

  override AstNode getBody() { result = MethodDefinition.super.getBody() }
}

private class ProgramAsCallable extends CallableImpl instanceof Program {
  override AstNode getRawParameter(int i) { none() }

  override AstNode getBody() { result = this }
}

class Parameter extends AstNode {
  private Callable function;
  private int index;

  Parameter() { this = function.getRawParameter(index) }

  Callable getCallable() { result = function }

  int getIndex() { result = index }
}

class RestParameter extends Parameter, RestPattern { }
