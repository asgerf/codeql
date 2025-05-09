private import codeql.js.common.CommonLayer

class PrefixUpdateExpression extends UpdateExpression {
  PrefixUpdateExpression() { this.getArgument().getParentIndex() = 1 }
}

class PostfixUpdateExpression extends UpdateExpression {
  PostfixUpdateExpression() { this.getArgument().getParentIndex() = 0 }
}
