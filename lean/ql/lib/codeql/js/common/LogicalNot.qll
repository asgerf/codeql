private import codeql.js.common.CommonLayer

class LogicalNot extends UnaryExpression {
  LogicalNot() { this.getOperator() = "!" }
}
