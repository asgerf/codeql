/**
 * Defines some additional predicates on `Callable` with some dependencies we don't want in the base layer.
 */

private import All

final private class FinalCallableBase = CallableBase;

class Callable extends FinalCallableBase {
  Parameter getParameter(int n) { result = super.getParameter(n) }

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

  predicate isAsync() {
    exists(Token asyncToken |
      asyncToken.getValue() = "async" and
      asyncToken.getParent() = this
    )
  }
}

class Parameter extends AstNode {
  private CallableBase function;
  private int index;

  Parameter() { this = function.getParameter(index) }

  Callable getCallable() { result = function }

  int getIndex() { result = index }
}

class RestParameter extends Parameter, RestPattern { }
