/**
 * CodeQL library for JS
 * Automatically generated from the tree-sitter grammar; do not edit
 */

import codeql.Locations as L

module JS {
  /** The base class for all AST nodes */
  class AstNode extends @js_ast_node {
    /** Gets a string representation of this element. */
    string toString() { result = this.getAPrimaryQlClass() }

    /** Gets the location of this element. */
    final L::Location getLocation() { js_ast_node_location(this, result) }

    /** Gets the parent of this element. */
    final AstNode getParent() { js_ast_node_parent(this, result, _) }

    /** Gets the index of this node among the children of its parent. */
    final int getParentIndex() { js_ast_node_parent(this, _, result) }

    /** Gets a field or child node of this node. */
    AstNode getAFieldOrChild() { none() }

    /** Gets the name of the primary QL class for this element. */
    string getAPrimaryQlClass() { result = "???" }

    /** Gets a comma-separated list of the names of the primary CodeQL classes to which this element belongs. */
    string getPrimaryQlClasses() { result = concat(this.getAPrimaryQlClass(), ",") }
  }

  /** A token. */
  class Token extends @js_token, AstNode {
    /** Gets the value of this token. */
    final string getValue() { js_tokeninfo(this, _, result) }

    /** Gets a string representation of this element. */
    final override string toString() { result = this.getValue() }

    /** Gets the name of the primary QL class for this element. */
    override string getAPrimaryQlClass() { result = "Token" }
  }

  /** A reserved word. */
  class ReservedWord extends @js_reserved_word, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ReservedWord" }
  }

  /** A class representing `arguments` nodes. */
  class Arguments extends @js_arguments, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Arguments" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_arguments_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_arguments_child(this, _, result) }
  }

  /** A class representing `array` nodes. */
  class Array extends @js_array, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Array" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_array_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_array_child(this, _, result) }
  }

  /** A class representing `array_pattern` nodes. */
  class ArrayPattern extends @js_array_pattern, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ArrayPattern" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_array_pattern_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_array_pattern_child(this, _, result) }
  }

  /** A class representing `arrow_function` nodes. */
  class ArrowFunction extends @js_arrow_function, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ArrowFunction" }

    /** Gets the node corresponding to the field `body`. */
    final AstNode getBody() { js_arrow_function_def(this, result) }

    /** Gets the node corresponding to the field `parameter`. */
    final Identifier getParameter() { js_arrow_function_parameter(this, result) }

    /** Gets the node corresponding to the field `parameters`. */
    final FormalParameters getParameters() { js_arrow_function_parameters(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_arrow_function_def(this, result) or
      js_arrow_function_parameter(this, result) or
      js_arrow_function_parameters(this, result)
    }
  }

  /** A class representing `assignment_expression` nodes. */
  class AssignmentExpression extends @js_assignment_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "AssignmentExpression" }

    /** Gets the node corresponding to the field `left`. */
    final AstNode getLeft() { js_assignment_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `right`. */
    final Expression getRight() { js_assignment_expression_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_assignment_expression_def(this, result, _) or js_assignment_expression_def(this, _, result)
    }
  }

  /** A class representing `assignment_pattern` nodes. */
  class AssignmentPattern extends @js_assignment_pattern, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "AssignmentPattern" }

    /** Gets the node corresponding to the field `left`. */
    final Pattern getLeft() { js_assignment_pattern_def(this, result, _) }

    /** Gets the node corresponding to the field `right`. */
    final Expression getRight() { js_assignment_pattern_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_assignment_pattern_def(this, result, _) or js_assignment_pattern_def(this, _, result)
    }
  }

  /** A class representing `augmented_assignment_expression` nodes. */
  class AugmentedAssignmentExpression extends @js_augmented_assignment_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "AugmentedAssignmentExpression" }

    /** Gets the node corresponding to the field `left`. */
    final AstNode getLeft() { js_augmented_assignment_expression_def(this, result, _, _) }

    /** Gets the node corresponding to the field `operator`. */
    final string getOperator() {
      exists(int value | js_augmented_assignment_expression_def(this, _, value, _) |
        result = "%=" and value = 0
        or
        result = "&&=" and value = 1
        or
        result = "&=" and value = 2
        or
        result = "**=" and value = 3
        or
        result = "*=" and value = 4
        or
        result = "+=" and value = 5
        or
        result = "-=" and value = 6
        or
        result = "/=" and value = 7
        or
        result = "<<=" and value = 8
        or
        result = ">>=" and value = 9
        or
        result = ">>>=" and value = 10
        or
        result = "??=" and value = 11
        or
        result = "^=" and value = 12
        or
        result = "|=" and value = 13
        or
        result = "||=" and value = 14
      )
    }

    /** Gets the node corresponding to the field `right`. */
    final Expression getRight() { js_augmented_assignment_expression_def(this, _, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_augmented_assignment_expression_def(this, result, _, _) or
      js_augmented_assignment_expression_def(this, _, _, result)
    }
  }

  /** A class representing `await_expression` nodes. */
  class AwaitExpression extends @js_await_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "AwaitExpression" }

    /** Gets the child of this node. */
    final Expression getChild() { js_await_expression_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_await_expression_def(this, result) }
  }

  /** A class representing `binary_expression` nodes. */
  class BinaryExpression extends @js_binary_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "BinaryExpression" }

    /** Gets the node corresponding to the field `left`. */
    final AstNode getLeft() { js_binary_expression_def(this, result, _, _) }

    /** Gets the node corresponding to the field `operator`. */
    final string getOperator() {
      exists(int value | js_binary_expression_def(this, _, value, _) |
        result = "!=" and value = 0
        or
        result = "!==" and value = 1
        or
        result = "%" and value = 2
        or
        result = "&" and value = 3
        or
        result = "&&" and value = 4
        or
        result = "*" and value = 5
        or
        result = "**" and value = 6
        or
        result = "+" and value = 7
        or
        result = "-" and value = 8
        or
        result = "/" and value = 9
        or
        result = "<" and value = 10
        or
        result = "<<" and value = 11
        or
        result = "<=" and value = 12
        or
        result = "==" and value = 13
        or
        result = "===" and value = 14
        or
        result = ">" and value = 15
        or
        result = ">=" and value = 16
        or
        result = ">>" and value = 17
        or
        result = ">>>" and value = 18
        or
        result = "??" and value = 19
        or
        result = "^" and value = 20
        or
        result = "in" and value = 21
        or
        result = "instanceof" and value = 22
        or
        result = "|" and value = 23
        or
        result = "||" and value = 24
      )
    }

    /** Gets the node corresponding to the field `right`. */
    final Expression getRight() { js_binary_expression_def(this, _, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_binary_expression_def(this, result, _, _) or js_binary_expression_def(this, _, _, result)
    }
  }

  /** A class representing `break_statement` nodes. */
  class BreakStatement extends @js_break_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "BreakStatement" }

    /** Gets the node corresponding to the field `label`. */
    final StatementIdentifier getLabel() { js_break_statement_label(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_break_statement_label(this, result) }
  }

  /** A class representing `call_expression` nodes. */
  class CallExpression extends @js_call_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "CallExpression" }

    /** Gets the node corresponding to the field `arguments`. */
    final AstNode getArguments() { js_call_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `function`. */
    final AstNode getFunction() { js_call_expression_def(this, _, result) }

    /** Gets the node corresponding to the field `optional_chain`. */
    final OptionalChain getOptionalChain() { js_call_expression_optional_chain(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_call_expression_def(this, result, _) or
      js_call_expression_def(this, _, result) or
      js_call_expression_optional_chain(this, result)
    }
  }

  /** A class representing `catch_clause` nodes. */
  class CatchClause extends @js_catch_clause, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "CatchClause" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_catch_clause_def(this, result) }

    /** Gets the node corresponding to the field `parameter`. */
    final AstNode getParameter() { js_catch_clause_parameter(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_catch_clause_def(this, result) or js_catch_clause_parameter(this, result)
    }
  }

  /** A class representing `class` nodes. */
  class Class extends @js_class, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Class" }

    /** Gets the node corresponding to the field `body`. */
    final ClassBody getBody() { js_class_def(this, result) }

    /** Gets the node corresponding to the field `decorator`. */
    final Decorator getDecorator(int i) { js_class_decorator(this, i, result) }

    /** Gets the node corresponding to the field `name`. */
    final Identifier getName() { js_class_name(this, result) }

    /** Gets the child of this node. */
    final ClassHeritage getChild() { js_class_child(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_class_def(this, result) or
      js_class_decorator(this, _, result) or
      js_class_name(this, result) or
      js_class_child(this, result)
    }
  }

  /** A class representing `class_body` nodes. */
  class ClassBody extends @js_class_body, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ClassBody" }

    /** Gets the node corresponding to the field `member`. */
    final AstNode getMember(int i) { js_class_body_member(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_class_body_member(this, _, result) }
  }

  /** A class representing `class_declaration` nodes. */
  class ClassDeclaration extends @js_class_declaration, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ClassDeclaration" }

    /** Gets the node corresponding to the field `body`. */
    final ClassBody getBody() { js_class_declaration_def(this, result, _) }

    /** Gets the node corresponding to the field `decorator`. */
    final Decorator getDecorator(int i) { js_class_declaration_decorator(this, i, result) }

    /** Gets the node corresponding to the field `name`. */
    final Identifier getName() { js_class_declaration_def(this, _, result) }

    /** Gets the child of this node. */
    final ClassHeritage getChild() { js_class_declaration_child(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_class_declaration_def(this, result, _) or
      js_class_declaration_decorator(this, _, result) or
      js_class_declaration_def(this, _, result) or
      js_class_declaration_child(this, result)
    }
  }

  /** A class representing `class_heritage` nodes. */
  class ClassHeritage extends @js_class_heritage, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ClassHeritage" }

    /** Gets the child of this node. */
    final Expression getChild() { js_class_heritage_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_class_heritage_def(this, result) }
  }

  /** A class representing `class_static_block` nodes. */
  class ClassStaticBlock extends @js_class_static_block, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ClassStaticBlock" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_class_static_block_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_class_static_block_def(this, result) }
  }

  /** A class representing `comment` tokens. */
  class Comment extends @js_token_comment, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Comment" }
  }

  /** A class representing `computed_property_name` nodes. */
  class ComputedPropertyName extends @js_computed_property_name, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ComputedPropertyName" }

    /** Gets the child of this node. */
    final Expression getChild() { js_computed_property_name_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_computed_property_name_def(this, result) }
  }

  /** A class representing `continue_statement` nodes. */
  class ContinueStatement extends @js_continue_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ContinueStatement" }

    /** Gets the node corresponding to the field `label`. */
    final StatementIdentifier getLabel() { js_continue_statement_label(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_continue_statement_label(this, result) }
  }

  /** A class representing `debugger_statement` tokens. */
  class DebuggerStatement extends @js_token_debugger_statement, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "DebuggerStatement" }
  }

  class Declaration extends @js_declaration, AstNode { }

  /** A class representing `decorator` nodes. */
  class Decorator extends @js_decorator, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Decorator" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_decorator_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_decorator_def(this, result) }
  }

  /** A class representing `do_statement` nodes. */
  class DoStatement extends @js_do_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "DoStatement" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody() { js_do_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `condition`. */
    final ParenthesizedExpression getCondition() { js_do_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_do_statement_def(this, result, _) or js_do_statement_def(this, _, result)
    }
  }

  /** A class representing `else_clause` nodes. */
  class ElseClause extends @js_else_clause, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ElseClause" }

    /** Gets the child of this node. */
    final Statement getChild() { js_else_clause_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_else_clause_def(this, result) }
  }

  /** A class representing `empty_statement` tokens. */
  class EmptyStatement extends @js_token_empty_statement, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "EmptyStatement" }
  }

  /** A class representing `escape_sequence` tokens. */
  class EscapeSequence extends @js_token_escape_sequence, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "EscapeSequence" }
  }

  /** A class representing `export_clause` nodes. */
  class ExportClause extends @js_export_clause, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ExportClause" }

    /** Gets the `i`th child of this node. */
    final ExportSpecifier getChild(int i) { js_export_clause_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_export_clause_child(this, _, result) }
  }

  /** A class representing `export_specifier` nodes. */
  class ExportSpecifier extends @js_export_specifier, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ExportSpecifier" }

    /** Gets the node corresponding to the field `alias`. */
    final AstNode getAlias() { js_export_specifier_alias(this, result) }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_export_specifier_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_export_specifier_alias(this, result) or js_export_specifier_def(this, result)
    }
  }

  /** A class representing `export_statement` nodes. */
  class ExportStatement extends @js_export_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ExportStatement" }

    /** Gets the node corresponding to the field `declaration`. */
    final Declaration getDeclaration() { js_export_statement_declaration(this, result) }

    /** Gets the node corresponding to the field `decorator`. */
    final Decorator getDecorator(int i) { js_export_statement_decorator(this, i, result) }

    /** Gets the node corresponding to the field `source`. */
    final String getSource() { js_export_statement_source(this, result) }

    /** Gets the node corresponding to the field `value`. */
    final Expression getValue() { js_export_statement_value(this, result) }

    /** Gets the child of this node. */
    final AstNode getChild() { js_export_statement_child(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_export_statement_declaration(this, result) or
      js_export_statement_decorator(this, _, result) or
      js_export_statement_source(this, result) or
      js_export_statement_value(this, result) or
      js_export_statement_child(this, result)
    }
  }

  class Expression extends @js_expression, AstNode { }

  /** A class representing `expression_statement` nodes. */
  class ExpressionStatement extends @js_expression_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ExpressionStatement" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_expression_statement_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_expression_statement_def(this, result) }
  }

  /** A class representing `false` tokens. */
  class False extends @js_token_false, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "False" }
  }

  /** A class representing `field_definition` nodes. */
  class FieldDefinition extends @js_field_definition, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "FieldDefinition" }

    /** Gets the node corresponding to the field `decorator`. */
    final Decorator getDecorator(int i) { js_field_definition_decorator(this, i, result) }

    /** Gets the node corresponding to the field `property`. */
    final AstNode getProperty() { js_field_definition_def(this, result) }

    /** Gets the node corresponding to the field `value`. */
    final Expression getValue() { js_field_definition_value(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_field_definition_decorator(this, _, result) or
      js_field_definition_def(this, result) or
      js_field_definition_value(this, result)
    }
  }

  /** A class representing `finally_clause` nodes. */
  class FinallyClause extends @js_finally_clause, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "FinallyClause" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_finally_clause_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_finally_clause_def(this, result) }
  }

  /** A class representing `for_in_statement` nodes. */
  class ForInStatement extends @js_for_in_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ForInStatement" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody() { js_for_in_statement_def(this, result, _, _, _) }

    /** Gets the node corresponding to the field `kind`. */
    final AstNode getKind() { js_for_in_statement_kind(this, result) }

    /** Gets the node corresponding to the field `left`. */
    final AstNode getLeft() { js_for_in_statement_def(this, _, result, _, _) }

    /** Gets the node corresponding to the field `operator`. */
    final string getOperator() {
      exists(int value | js_for_in_statement_def(this, _, _, value, _) |
        result = "in" and value = 0
        or
        result = "of" and value = 1
      )
    }

    /** Gets the node corresponding to the field `right`. */
    final AstNode getRight() { js_for_in_statement_def(this, _, _, _, result) }

    /** Gets the node corresponding to the field `value`. */
    final Expression getValue() { js_for_in_statement_value(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_for_in_statement_def(this, result, _, _, _) or
      js_for_in_statement_kind(this, result) or
      js_for_in_statement_def(this, _, result, _, _) or
      js_for_in_statement_def(this, _, _, _, result) or
      js_for_in_statement_value(this, result)
    }
  }

  /** A class representing `for_statement` nodes. */
  class ForStatement extends @js_for_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ForStatement" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody() { js_for_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `condition`. */
    final AstNode getCondition(int i) { js_for_statement_condition(this, i, result) }

    /** Gets the node corresponding to the field `increment`. */
    final AstNode getIncrement() { js_for_statement_increment(this, result) }

    /** Gets the node corresponding to the field `initializer`. */
    final AstNode getInitializer() { js_for_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_for_statement_def(this, result, _) or
      js_for_statement_condition(this, _, result) or
      js_for_statement_increment(this, result) or
      js_for_statement_def(this, _, result)
    }
  }

  /** A class representing `formal_parameters` nodes. */
  class FormalParameters extends @js_formal_parameters, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "FormalParameters" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_formal_parameters_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_formal_parameters_child(this, _, result) }
  }

  /** A class representing `function_declaration` nodes. */
  class FunctionDeclaration extends @js_function_declaration, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "FunctionDeclaration" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_function_declaration_def(this, result, _, _) }

    /** Gets the node corresponding to the field `name`. */
    final Identifier getName() { js_function_declaration_def(this, _, result, _) }

    /** Gets the node corresponding to the field `parameters`. */
    final FormalParameters getParameters() { js_function_declaration_def(this, _, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_function_declaration_def(this, result, _, _) or
      js_function_declaration_def(this, _, result, _) or
      js_function_declaration_def(this, _, _, result)
    }
  }

  /** A class representing `function_expression` nodes. */
  class FunctionExpression extends @js_function_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "FunctionExpression" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_function_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `name`. */
    final Identifier getName() { js_function_expression_name(this, result) }

    /** Gets the node corresponding to the field `parameters`. */
    final FormalParameters getParameters() { js_function_expression_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_function_expression_def(this, result, _) or
      js_function_expression_name(this, result) or
      js_function_expression_def(this, _, result)
    }
  }

  /** A class representing `generator_function` nodes. */
  class GeneratorFunction extends @js_generator_function, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "GeneratorFunction" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_generator_function_def(this, result, _) }

    /** Gets the node corresponding to the field `name`. */
    final Identifier getName() { js_generator_function_name(this, result) }

    /** Gets the node corresponding to the field `parameters`. */
    final FormalParameters getParameters() { js_generator_function_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_generator_function_def(this, result, _) or
      js_generator_function_name(this, result) or
      js_generator_function_def(this, _, result)
    }
  }

  /** A class representing `generator_function_declaration` nodes. */
  class GeneratorFunctionDeclaration extends @js_generator_function_declaration, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "GeneratorFunctionDeclaration" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_generator_function_declaration_def(this, result, _, _) }

    /** Gets the node corresponding to the field `name`. */
    final Identifier getName() { js_generator_function_declaration_def(this, _, result, _) }

    /** Gets the node corresponding to the field `parameters`. */
    final FormalParameters getParameters() {
      js_generator_function_declaration_def(this, _, _, result)
    }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_generator_function_declaration_def(this, result, _, _) or
      js_generator_function_declaration_def(this, _, result, _) or
      js_generator_function_declaration_def(this, _, _, result)
    }
  }

  /** A class representing `hash_bang_line` tokens. */
  class HashBangLine extends @js_token_hash_bang_line, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "HashBangLine" }
  }

  /** A class representing `html_character_reference` tokens. */
  class HtmlCharacterReference extends @js_token_html_character_reference, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "HtmlCharacterReference" }
  }

  /** A class representing `html_comment` tokens. */
  class HtmlComment extends @js_token_html_comment, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "HtmlComment" }
  }

  /** A class representing `identifier` tokens. */
  class Identifier extends @js_token_identifier, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Identifier" }
  }

  /** A class representing `if_statement` nodes. */
  class IfStatement extends @js_if_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "IfStatement" }

    /** Gets the node corresponding to the field `alternative`. */
    final ElseClause getAlternative() { js_if_statement_alternative(this, result) }

    /** Gets the node corresponding to the field `condition`. */
    final ParenthesizedExpression getCondition() { js_if_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `consequence`. */
    final Statement getConsequence() { js_if_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_if_statement_alternative(this, result) or
      js_if_statement_def(this, result, _) or
      js_if_statement_def(this, _, result)
    }
  }

  /** A class representing `import` tokens. */
  class Import extends @js_token_import, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Import" }
  }

  /** A class representing `import_attribute` nodes. */
  class ImportAttribute extends @js_import_attribute, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ImportAttribute" }

    /** Gets the child of this node. */
    final Object getChild() { js_import_attribute_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_import_attribute_def(this, result) }
  }

  /** A class representing `import_clause` nodes. */
  class ImportClause extends @js_import_clause, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ImportClause" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_import_clause_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_import_clause_child(this, _, result) }
  }

  /** A class representing `import_specifier` nodes. */
  class ImportSpecifier extends @js_import_specifier, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ImportSpecifier" }

    /** Gets the node corresponding to the field `alias`. */
    final Identifier getAlias() { js_import_specifier_alias(this, result) }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_import_specifier_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_import_specifier_alias(this, result) or js_import_specifier_def(this, result)
    }
  }

  /** A class representing `import_statement` nodes. */
  class ImportStatement extends @js_import_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ImportStatement" }

    /** Gets the node corresponding to the field `source`. */
    final String getSource() { js_import_statement_def(this, result) }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_import_statement_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_import_statement_def(this, result) or js_import_statement_child(this, _, result)
    }
  }

  /** A class representing `jsx_attribute` nodes. */
  class JsxAttribute extends @js_jsx_attribute, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxAttribute" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_jsx_attribute_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_jsx_attribute_child(this, _, result) }
  }

  /** A class representing `jsx_closing_element` nodes. */
  class JsxClosingElement extends @js_jsx_closing_element, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxClosingElement" }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_jsx_closing_element_name(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_jsx_closing_element_name(this, result) }
  }

  /** A class representing `jsx_element` nodes. */
  class JsxElement extends @js_jsx_element, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxElement" }

    /** Gets the node corresponding to the field `close_tag`. */
    final JsxClosingElement getCloseTag() { js_jsx_element_def(this, result, _) }

    /** Gets the node corresponding to the field `open_tag`. */
    final JsxOpeningElement getOpenTag() { js_jsx_element_def(this, _, result) }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_jsx_element_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_jsx_element_def(this, result, _) or
      js_jsx_element_def(this, _, result) or
      js_jsx_element_child(this, _, result)
    }
  }

  /** A class representing `jsx_expression` nodes. */
  class JsxExpression extends @js_jsx_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxExpression" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_jsx_expression_child(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_jsx_expression_child(this, result) }
  }

  /** A class representing `jsx_namespace_name` nodes. */
  class JsxNamespaceName extends @js_jsx_namespace_name, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxNamespaceName" }

    /** Gets the `i`th child of this node. */
    final Identifier getChild(int i) { js_jsx_namespace_name_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_jsx_namespace_name_child(this, _, result) }
  }

  /** A class representing `jsx_opening_element` nodes. */
  class JsxOpeningElement extends @js_jsx_opening_element, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxOpeningElement" }

    /** Gets the node corresponding to the field `attribute`. */
    final AstNode getAttribute(int i) { js_jsx_opening_element_attribute(this, i, result) }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_jsx_opening_element_name(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_jsx_opening_element_attribute(this, _, result) or js_jsx_opening_element_name(this, result)
    }
  }

  /** A class representing `jsx_self_closing_element` nodes. */
  class JsxSelfClosingElement extends @js_jsx_self_closing_element, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxSelfClosingElement" }

    /** Gets the node corresponding to the field `attribute`. */
    final AstNode getAttribute(int i) { js_jsx_self_closing_element_attribute(this, i, result) }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_jsx_self_closing_element_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_jsx_self_closing_element_attribute(this, _, result) or
      js_jsx_self_closing_element_def(this, result)
    }
  }

  /** A class representing `jsx_text` tokens. */
  class JsxText extends @js_token_jsx_text, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "JsxText" }
  }

  /** A class representing `labeled_statement` nodes. */
  class LabeledStatement extends @js_labeled_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "LabeledStatement" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody() { js_labeled_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `label`. */
    final StatementIdentifier getLabel() { js_labeled_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_labeled_statement_def(this, result, _) or js_labeled_statement_def(this, _, result)
    }
  }

  /** A class representing `lexical_declaration` nodes. */
  class LexicalDeclaration extends @js_lexical_declaration, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "LexicalDeclaration" }

    /** Gets the node corresponding to the field `kind`. */
    final string getKind() {
      exists(int value | js_lexical_declaration_def(this, value) |
        result = "const" and value = 0
        or
        result = "let" and value = 1
      )
    }

    /** Gets the `i`th child of this node. */
    final VariableDeclarator getChild(int i) { js_lexical_declaration_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_lexical_declaration_child(this, _, result) }
  }

  /** A class representing `member_expression` nodes. */
  class MemberExpression extends @js_member_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "MemberExpression" }

    /** Gets the node corresponding to the field `object`. */
    final AstNode getObject() { js_member_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `optional_chain`. */
    final OptionalChain getOptionalChain() { js_member_expression_optional_chain(this, result) }

    /** Gets the node corresponding to the field `property`. */
    final AstNode getProperty() { js_member_expression_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_member_expression_def(this, result, _) or
      js_member_expression_optional_chain(this, result) or
      js_member_expression_def(this, _, result)
    }
  }

  /** A class representing `meta_property` tokens. */
  class MetaProperty extends @js_token_meta_property, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "MetaProperty" }
  }

  /** A class representing `method_definition` nodes. */
  class MethodDefinition extends @js_method_definition, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "MethodDefinition" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_method_definition_def(this, result, _, _) }

    /** Gets the node corresponding to the field `decorator`. */
    final Decorator getDecorator(int i) { js_method_definition_decorator(this, i, result) }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_method_definition_def(this, _, result, _) }

    /** Gets the node corresponding to the field `parameters`. */
    final FormalParameters getParameters() { js_method_definition_def(this, _, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_method_definition_def(this, result, _, _) or
      js_method_definition_decorator(this, _, result) or
      js_method_definition_def(this, _, result, _) or
      js_method_definition_def(this, _, _, result)
    }
  }

  /** A class representing `named_imports` nodes. */
  class NamedImports extends @js_named_imports, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "NamedImports" }

    /** Gets the `i`th child of this node. */
    final ImportSpecifier getChild(int i) { js_named_imports_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_named_imports_child(this, _, result) }
  }

  /** A class representing `namespace_export` nodes. */
  class NamespaceExport extends @js_namespace_export, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "NamespaceExport" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_namespace_export_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_namespace_export_def(this, result) }
  }

  /** A class representing `namespace_import` nodes. */
  class NamespaceImport extends @js_namespace_import, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "NamespaceImport" }

    /** Gets the child of this node. */
    final Identifier getChild() { js_namespace_import_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_namespace_import_def(this, result) }
  }

  /** A class representing `new_expression` nodes. */
  class NewExpression extends @js_new_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "NewExpression" }

    /** Gets the node corresponding to the field `arguments`. */
    final Arguments getArguments() { js_new_expression_arguments(this, result) }

    /** Gets the node corresponding to the field `constructor`. */
    final AstNode getConstructor() { js_new_expression_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_new_expression_arguments(this, result) or js_new_expression_def(this, result)
    }
  }

  /** A class representing `null` tokens. */
  class Null extends @js_token_null, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Null" }
  }

  /** A class representing `number` tokens. */
  class Number extends @js_token_number, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Number" }
  }

  /** A class representing `object` nodes. */
  class Object extends @js_object, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Object" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_object_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_object_child(this, _, result) }
  }

  /** A class representing `object_assignment_pattern` nodes. */
  class ObjectAssignmentPattern extends @js_object_assignment_pattern, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ObjectAssignmentPattern" }

    /** Gets the node corresponding to the field `left`. */
    final AstNode getLeft() { js_object_assignment_pattern_def(this, result, _) }

    /** Gets the node corresponding to the field `right`. */
    final Expression getRight() { js_object_assignment_pattern_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_object_assignment_pattern_def(this, result, _) or
      js_object_assignment_pattern_def(this, _, result)
    }
  }

  /** A class representing `object_pattern` nodes. */
  class ObjectPattern extends @js_object_pattern, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ObjectPattern" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_object_pattern_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_object_pattern_child(this, _, result) }
  }

  /** A class representing `optional_chain` tokens. */
  class OptionalChain extends @js_token_optional_chain, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "OptionalChain" }
  }

  /** A class representing `pair` nodes. */
  class Pair extends @js_pair, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Pair" }

    /** Gets the node corresponding to the field `key`. */
    final AstNode getKey() { js_pair_def(this, result, _) }

    /** Gets the node corresponding to the field `value`. */
    final Expression getValue() { js_pair_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_pair_def(this, result, _) or js_pair_def(this, _, result)
    }
  }

  /** A class representing `pair_pattern` nodes. */
  class PairPattern extends @js_pair_pattern, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "PairPattern" }

    /** Gets the node corresponding to the field `key`. */
    final AstNode getKey() { js_pair_pattern_def(this, result, _) }

    /** Gets the node corresponding to the field `value`. */
    final AstNode getValue() { js_pair_pattern_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_pair_pattern_def(this, result, _) or js_pair_pattern_def(this, _, result)
    }
  }

  /** A class representing `parenthesized_expression` nodes. */
  class ParenthesizedExpression extends @js_parenthesized_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ParenthesizedExpression" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_parenthesized_expression_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_parenthesized_expression_def(this, result) }
  }

  class Pattern extends @js_pattern, AstNode { }

  class PrimaryExpression extends @js_primary_expression, AstNode { }

  /** A class representing `private_property_identifier` tokens. */
  class PrivatePropertyIdentifier extends @js_token_private_property_identifier, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "PrivatePropertyIdentifier" }
  }

  /** A class representing `program` nodes. */
  class Program extends @js_program, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Program" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_program_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_program_child(this, _, result) }
  }

  /** A class representing `property_identifier` tokens. */
  class PropertyIdentifier extends @js_token_property_identifier, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "PropertyIdentifier" }
  }

  /** A class representing `regex` nodes. */
  class Regex extends @js_regex, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Regex" }

    /** Gets the node corresponding to the field `flags`. */
    final RegexFlags getFlags() { js_regex_flags(this, result) }

    /** Gets the node corresponding to the field `pattern`. */
    final RegexPattern getPattern() { js_regex_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_regex_flags(this, result) or js_regex_def(this, result)
    }
  }

  /** A class representing `regex_flags` tokens. */
  class RegexFlags extends @js_token_regex_flags, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "RegexFlags" }
  }

  /** A class representing `regex_pattern` tokens. */
  class RegexPattern extends @js_token_regex_pattern, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "RegexPattern" }
  }

  /** A class representing `rest_pattern` nodes. */
  class RestPattern extends @js_rest_pattern, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "RestPattern" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_rest_pattern_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_rest_pattern_def(this, result) }
  }

  /** A class representing `return_statement` nodes. */
  class ReturnStatement extends @js_return_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ReturnStatement" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_return_statement_child(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_return_statement_child(this, result) }
  }

  /** A class representing `sequence_expression` nodes. */
  class SequenceExpression extends @js_sequence_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SequenceExpression" }

    /** Gets the `i`th child of this node. */
    final Expression getChild(int i) { js_sequence_expression_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_sequence_expression_child(this, _, result) }
  }

  /** A class representing `shorthand_property_identifier` tokens. */
  class ShorthandPropertyIdentifier extends @js_token_shorthand_property_identifier, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ShorthandPropertyIdentifier" }
  }

  /** A class representing `shorthand_property_identifier_pattern` tokens. */
  class ShorthandPropertyIdentifierPattern extends @js_token_shorthand_property_identifier_pattern,
    Token
  {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ShorthandPropertyIdentifierPattern" }
  }

  /** A class representing `spread_element` nodes. */
  class SpreadElement extends @js_spread_element, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SpreadElement" }

    /** Gets the child of this node. */
    final Expression getChild() { js_spread_element_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_spread_element_def(this, result) }
  }

  class Statement extends @js_statement, AstNode { }

  /** A class representing `statement_block` nodes. */
  class StatementBlock extends @js_statement_block, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "StatementBlock" }

    /** Gets the `i`th child of this node. */
    final Statement getChild(int i) { js_statement_block_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_statement_block_child(this, _, result) }
  }

  /** A class representing `statement_identifier` tokens. */
  class StatementIdentifier extends @js_token_statement_identifier, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "StatementIdentifier" }
  }

  /** A class representing `string` nodes. */
  class String extends @js_string__, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "String" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_string_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_string_child(this, _, result) }
  }

  /** A class representing `string_fragment` tokens. */
  class StringFragment extends @js_token_string_fragment, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "StringFragment" }
  }

  /** A class representing `subscript_expression` nodes. */
  class SubscriptExpression extends @js_subscript_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SubscriptExpression" }

    /** Gets the node corresponding to the field `index`. */
    final AstNode getIndex() { js_subscript_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `object`. */
    final Expression getObject() { js_subscript_expression_def(this, _, result) }

    /** Gets the node corresponding to the field `optional_chain`. */
    final OptionalChain getOptionalChain() { js_subscript_expression_optional_chain(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_subscript_expression_def(this, result, _) or
      js_subscript_expression_def(this, _, result) or
      js_subscript_expression_optional_chain(this, result)
    }
  }

  /** A class representing `super` tokens. */
  class Super extends @js_token_super, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Super" }
  }

  /** A class representing `switch_body` nodes. */
  class SwitchBody extends @js_switch_body, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SwitchBody" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_switch_body_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_switch_body_child(this, _, result) }
  }

  /** A class representing `switch_case` nodes. */
  class SwitchCase extends @js_switch_case, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SwitchCase" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody(int i) { js_switch_case_body(this, i, result) }

    /** Gets the node corresponding to the field `value`. */
    final AstNode getValue() { js_switch_case_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_switch_case_body(this, _, result) or js_switch_case_def(this, result)
    }
  }

  /** A class representing `switch_default` nodes. */
  class SwitchDefault extends @js_switch_default, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SwitchDefault" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody(int i) { js_switch_default_body(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_switch_default_body(this, _, result) }
  }

  /** A class representing `switch_statement` nodes. */
  class SwitchStatement extends @js_switch_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "SwitchStatement" }

    /** Gets the node corresponding to the field `body`. */
    final SwitchBody getBody() { js_switch_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `value`. */
    final ParenthesizedExpression getValue() { js_switch_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_switch_statement_def(this, result, _) or js_switch_statement_def(this, _, result)
    }
  }

  /** A class representing `template_string` nodes. */
  class TemplateString extends @js_template_string, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "TemplateString" }

    /** Gets the `i`th child of this node. */
    final AstNode getChild(int i) { js_template_string_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_template_string_child(this, _, result) }
  }

  /** A class representing `template_substitution` nodes. */
  class TemplateSubstitution extends @js_template_substitution, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "TemplateSubstitution" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_template_substitution_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_template_substitution_def(this, result) }
  }

  /** A class representing `ternary_expression` nodes. */
  class TernaryExpression extends @js_ternary_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "TernaryExpression" }

    /** Gets the node corresponding to the field `alternative`. */
    final Expression getAlternative() { js_ternary_expression_def(this, result, _, _) }

    /** Gets the node corresponding to the field `condition`. */
    final Expression getCondition() { js_ternary_expression_def(this, _, result, _) }

    /** Gets the node corresponding to the field `consequence`. */
    final Expression getConsequence() { js_ternary_expression_def(this, _, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_ternary_expression_def(this, result, _, _) or
      js_ternary_expression_def(this, _, result, _) or
      js_ternary_expression_def(this, _, _, result)
    }
  }

  /** A class representing `this` tokens. */
  class This extends @js_token_this, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "This" }
  }

  /** A class representing `throw_statement` nodes. */
  class ThrowStatement extends @js_throw_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "ThrowStatement" }

    /** Gets the child of this node. */
    final AstNode getChild() { js_throw_statement_def(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_throw_statement_def(this, result) }
  }

  /** A class representing `true` tokens. */
  class True extends @js_token_true, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "True" }
  }

  /** A class representing `try_statement` nodes. */
  class TryStatement extends @js_try_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "TryStatement" }

    /** Gets the node corresponding to the field `body`. */
    final StatementBlock getBody() { js_try_statement_def(this, result) }

    /** Gets the node corresponding to the field `finalizer`. */
    final FinallyClause getFinalizer() { js_try_statement_finalizer(this, result) }

    /** Gets the node corresponding to the field `handler`. */
    final CatchClause getHandler() { js_try_statement_handler(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_try_statement_def(this, result) or
      js_try_statement_finalizer(this, result) or
      js_try_statement_handler(this, result)
    }
  }

  /** A class representing `unary_expression` nodes. */
  class UnaryExpression extends @js_unary_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "UnaryExpression" }

    /** Gets the node corresponding to the field `argument`. */
    final Expression getArgument() { js_unary_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `operator`. */
    final string getOperator() {
      exists(int value | js_unary_expression_def(this, _, value) |
        result = "!" and value = 0
        or
        result = "+" and value = 1
        or
        result = "-" and value = 2
        or
        result = "delete" and value = 3
        or
        result = "typeof" and value = 4
        or
        result = "void" and value = 5
        or
        result = "~" and value = 6
      )
    }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_unary_expression_def(this, result, _) }
  }

  /** A class representing `undefined` tokens. */
  class Undefined extends @js_token_undefined, Token {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "Undefined" }
  }

  /** A class representing `update_expression` nodes. */
  class UpdateExpression extends @js_update_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "UpdateExpression" }

    /** Gets the node corresponding to the field `argument`. */
    final Expression getArgument() { js_update_expression_def(this, result, _) }

    /** Gets the node corresponding to the field `operator`. */
    final string getOperator() {
      exists(int value | js_update_expression_def(this, _, value) |
        result = "++" and value = 0
        or
        result = "--" and value = 1
      )
    }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_update_expression_def(this, result, _) }
  }

  /** A class representing `variable_declaration` nodes. */
  class VariableDeclaration extends @js_variable_declaration, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "VariableDeclaration" }

    /** Gets the `i`th child of this node. */
    final VariableDeclarator getChild(int i) { js_variable_declaration_child(this, i, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_variable_declaration_child(this, _, result) }
  }

  /** A class representing `variable_declarator` nodes. */
  class VariableDeclarator extends @js_variable_declarator, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "VariableDeclarator" }

    /** Gets the node corresponding to the field `name`. */
    final AstNode getName() { js_variable_declarator_def(this, result) }

    /** Gets the node corresponding to the field `value`. */
    final Expression getValue() { js_variable_declarator_value(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_variable_declarator_def(this, result) or js_variable_declarator_value(this, result)
    }
  }

  /** A class representing `while_statement` nodes. */
  class WhileStatement extends @js_while_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "WhileStatement" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody() { js_while_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `condition`. */
    final ParenthesizedExpression getCondition() { js_while_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_while_statement_def(this, result, _) or js_while_statement_def(this, _, result)
    }
  }

  /** A class representing `with_statement` nodes. */
  class WithStatement extends @js_with_statement, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "WithStatement" }

    /** Gets the node corresponding to the field `body`. */
    final Statement getBody() { js_with_statement_def(this, result, _) }

    /** Gets the node corresponding to the field `object`. */
    final ParenthesizedExpression getObject() { js_with_statement_def(this, _, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() {
      js_with_statement_def(this, result, _) or js_with_statement_def(this, _, result)
    }
  }

  /** A class representing `yield_expression` nodes. */
  class YieldExpression extends @js_yield_expression, AstNode {
    /** Gets the name of the primary QL class for this element. */
    final override string getAPrimaryQlClass() { result = "YieldExpression" }

    /** Gets the child of this node. */
    final Expression getChild() { js_yield_expression_child(this, result) }

    /** Gets a field or child node of this node. */
    final override AstNode getAFieldOrChild() { js_yield_expression_child(this, result) }
  }
}
