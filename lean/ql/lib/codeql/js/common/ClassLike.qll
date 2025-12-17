private import All

/**
 * A class declaration or class expression.
 */
final class ClassLike = ClassLikeImpl;

abstract private class ClassLikeImpl extends AstNode {
  /** Gets the class body. */
  abstract ClassBody getBody();

  /** Gets the `i`th decorator. */
  abstract Decorator getDecorator(int i);

  /** Gets the node containing the declared name the class, if any. */
  abstract Identifier getNameNode();

  /** Gets the heritage clause of this class. */
  abstract ClassHeritage getHeritage();

  final string getName() {
    result = inferNameFromNode(this.getNameNode())
    or
    not exists(this.getNameNode()) and
    result = inferNameFromContext(this)
  }

  /**
   * Gets a synthetic node representing the prototype object created for this class.
   */
  final SyntheticNode getPrototypeObject() {
    result = this.getSyntheticChildNode("prototype-object")
  }

  /**
   * Gets the constructor of this class, if any.
   */
  final Callable getConstructor() {
    exists(MethodDefinition def |
      def = this.getBody().getMember(_) and
      def.getName().(PropertyIdentifier).getValue() = "constructor" and
      result = def
    )
  }
}

private class ClassExpressionAsImpl extends ClassLikeImpl instanceof Class {
  override ClassBody getBody() { result = Class.super.getBody() }

  override Decorator getDecorator(int i) { none() }

  override Identifier getNameNode() { result = Class.super.getName() }

  override ClassHeritage getHeritage() { result = Class.super.getChild() }
}

private class ClassDeclarationAsImpl extends ClassLikeImpl instanceof ClassDeclaration {
  override ClassBody getBody() { result = ClassDeclaration.super.getBody() }

  override Decorator getDecorator(int i) { result = ClassDeclaration.super.getDecorator(i) }

  override Identifier getNameNode() { result = ClassDeclaration.super.getName() }

  override ClassHeritage getHeritage() { result = ClassDeclaration.super.getChild() }
}
