private import javascript
private import semmle.javascript.dataflow.internal.DataFlowNode
cached
private predicate postUpdatePair(Node pre, Node post) {
  exists(AST::ValueNode expr |
    pre = TValueNode(expr) and
    post = TExprPostUpdateNode(expr)
  )
  or
  exists(NewExpr expr |
    pre = TConstructorThisArgumentNode(expr) and
    post = TValueNode(expr)
  )
  or
  exists(SuperCall expr |
    pre = TConstructorThisArgumentNode(expr) and
    post = TConstructorThisPostUpdate(expr.getBinder())
  )
  or
  exists(Function constructor |
    pre = TThisNode(constructor) and
    post = TConstructorThisPostUpdate(constructor)
  )
}

class PostUpdateNode extends DataFlow::Node {
  PostUpdateNode() { postUpdatePair(_, this) }

  final DataFlow::Node getPreUpdateNode() { postUpdatePair(result, this) }
}
