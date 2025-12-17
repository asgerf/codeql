private import All

/**
 * Base class for the `Callable` class containing only what is needed in the base layer.
 */
abstract class CallableBase extends AstNode {
  /** Gets the `i`th parameter of this function. */
  abstract AstNode getParameter(int i);

  int getNumParameter() { result = count(int i | exists(this.getParameter(i))) }

  abstract AstNode getBody();

  /**
   * Gets the identifier declared as part of this function, if any.
   */
  AstNode getNameNode() { none() }

  /**
   * Gets a synthetic node representing the `this` parameter of a callable.
   *
   * Has no result for arrow functions.
   */
  SyntheticNode getThisParameter() { result = this.getSyntheticChildNode("this-parameter") }

  /**
   * Gets a synthetic node representing a parameter holding a reference to the function
   * object being invoked.
   */
  SyntheticNode getFunctionSelfReferenceNode() {
    result = this.getSyntheticChildNode("function-self-reference")
  }
}

private class ArrowFunctionAsCallable extends CallableBase instanceof ArrowFunction {
  override AstNode getParameter(int i) {
    // `(x) => { ... }`
    result = super.getParameters().getChild(i)
    or
    // `x => {..}` (no parenthesis around parameter)
    result = super.getParameter() and i = 0
  }

  override AstNode getBody() { result = ArrowFunction.super.getBody() }
}

private class FunctionDeclarationAsCallable extends CallableBase instanceof FunctionDeclaration {
  override AstNode getParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = FunctionDeclaration.super.getName() }

  override AstNode getBody() { result = FunctionDeclaration.super.getBody() }
}

private class FunctionExpressionAsCallable extends CallableBase instanceof FunctionExpression {
  override AstNode getParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = FunctionExpression.super.getName() }

  override AstNode getBody() { result = FunctionExpression.super.getBody() }
}

private class GeneratorFunctionAsCallable extends CallableBase instanceof GeneratorFunction {
  override AstNode getParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = GeneratorFunction.super.getName() }

  override AstNode getBody() { result = GeneratorFunction.super.getBody() }
}

private class GeneratorFunctionDeclarationAsCallable extends CallableBase instanceof GeneratorFunctionDeclaration
{
  override AstNode getParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = GeneratorFunctionDeclaration.super.getName() }

  override AstNode getBody() { result = GeneratorFunctionDeclaration.super.getBody() }
}

private class MethodDefinitionAsCallable extends CallableBase instanceof MethodDefinition {
  override AstNode getParameter(int i) { result = super.getParameters().getChild(i) }

  override AstNode getNameNode() { result = MethodDefinition.super.getName() }

  override AstNode getBody() { result = MethodDefinition.super.getBody() }
}

private class ProgramAsCallable extends CallableBase instanceof Program {
  override AstNode getParameter(int i) { none() }

  override AstNode getBody() { result = this }
}
