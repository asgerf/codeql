use codeql_extractor::extractor::simple;
use yeast::{rule, DesugaringConfig, PhaseKind};

fn translation_rules() -> Vec<yeast::Rule> {
    vec![
        // ---- Top-level ----
        rule!(
            (source_file (_)* @children)
            =>
            (top_level
                body: (block stmt: {..children})
            )
        ),
        // ---- Literals ----
        rule!((integer_literal) => (int_literal)),
        rule!((hex_literal) => (int_literal)),
        rule!((bin_literal) => (int_literal)),
        rule!((oct_literal) => (int_literal)),
        rule!((real_literal) => (float_literal)),
        rule!((boolean_literal) => (boolean_literal)),
        rule!((line_string_literal) => (string_literal)),
        rule!((multi_line_string_literal) => (string_literal)),
        rule!((raw_string_literal) => (string_literal)),
        rule!((regex_literal) => (regex_literal)),
        // ---- Names ----
        rule!((simple_identifier) @id => (name_expr identifier: (identifier #{id}))),
        // ---- Operators ----
        // All binary operators share the lhs/op/rhs shape.
        rule!((additive_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((multiplicative_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((comparison_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((equality_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((conjunction_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((disjunction_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((infix_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((range_expression start: (_) @l op: _ @op end: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((bitwise_operation lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((nil_coalescing_expression value: (_) @l if_nil: (_) @r) => (binary_expr left: {l} operator: (operator "??") right: {r})),
        // Prefix unary operators
        rule!((prefix_expression operation: _ @op target: (_) @operand) => (unary_expr operator: (operator #{op}) operand: {operand})),
        // Postfix unary operators
        rule!((postfix_expression operation: _ @op target: (_) @operand) => (unary_expr operator: (operator #{op}) operand: {operand})),
        // Parenthesised single-value tuple is a grouping expression; pass through.
        // Multi-value tuples become tuple_expr.
        rule!((tuple_expression value: (_)* @v) => (tuple_expr element: {..v})),
        // ---- Variables ----
        // Plain assignment: `x = expr`
        rule!(
            (assignment operator: "=" target: (directly_assignable_expression (_) @target) result: (_) @value)
            =>
            (assign_expr target: {target} value: {value})
        ),
        // Compound assignment: `x += expr` etc.
        rule!(
            (assignment operator: _ @op target: (directly_assignable_expression (_) @target) result: (_) @value)
            =>
            (compound_assign_expr target: {target} operator: (operator #{op}) value: {value})
        ),
        // Property declaration (let/var binding) with value
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (pattern bound_identifier: (_) @name)
                value: (_) @val)
            =>
            (variable_declaration
                modifier: (modifier #{binding_kind})
                pattern: (name_pattern identifier: (identifier #{name}))
                value: {val})
        ),
        // Property declaration (let/var binding) without value (type-only decl)
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (pattern bound_identifier: (_) @name))
            =>
            (variable_declaration
                modifier: (modifier #{binding_kind})
                pattern: (name_pattern identifier: (identifier #{name})))
        ),
        // Unwrap `type` wrapper node
        rule!((type name: (_) @inner) => {inner}),
        // User type → named_type_expr
        rule!((user_type (type_identifier) @name) => (named_type_expr name: (identifier #{name}))),
        // `directly_assignable_expression` is just a wrapper; unwrap it
        rule!((directly_assignable_expression (_) @inner) => {inner}),
        // Pattern with bound_identifier → name_pattern
        rule!((pattern bound_identifier: (_) @name) => (name_pattern identifier: (identifier #{name}))),
        // Tuple pattern (destructuring)
        rule!((pattern (pattern)* @elems) => (tuple_pattern element: {..elems})),
        // ---- Functions ----
        // Function declaration
        rule!(
            (function_declaration
                name: (_) @name
                (parameter)* @params
                body: (function_body (statements (_)* @body_stmts)))
            =>
            (function_declaration
                name: (identifier #{name})
                parameter: {..params}
                body: (block stmt: {..body_stmts}))
        ),
        // Function declaration with return type
        rule!(
            (function_declaration
                name: (_) @name
                (parameter)* @params
                return_type: (_) @ret
                body: (function_body (statements (_)* @body_stmts)))
            =>
            (function_declaration
                name: (identifier #{name})
                parameter: {..params}
                return_type: {ret}
                body: (block stmt: {..body_stmts}))
        ),
        // Function declaration with empty body
        rule!(
            (function_declaration
                name: (_) @name
                (parameter)* @params
                body: (function_body))
            =>
            (function_declaration
                name: (identifier #{name})
                parameter: {..params}
                body: (block))
        ),
        // Function declaration with return type and empty body
        rule!(
            (function_declaration
                name: (_) @name
                (parameter)* @params
                return_type: (_) @ret
                body: (function_body))
            =>
            (function_declaration
                name: (identifier #{name})
                parameter: {..params}
                return_type: {ret}
                body: (block))
        ),
        // Parameter with external name and type
        rule!(
            (parameter external_name: (_) @ext name: (_) @name)
            =>
            (parameter
                external_name: (identifier #{ext})
                pattern: (name_pattern identifier: (identifier #{name})))
        ),
        // Parameter with just name and type (no external name)
        rule!(
            (parameter name: (_) @name)
            =>
            (parameter
                pattern: (name_pattern identifier: (identifier #{name})))
        ),
        // Call expression: function(args...)
        rule!(
            (call_expression (_) @func (call_suffix (value_arguments (value_argument)* @args)))
            =>
            (call_expr function: {func} argument: {..args})
        ),
        // Value argument with label
        rule!(
            (value_argument name: (value_argument_label (_) @label) value: (_) @val)
            =>
            (argument name: (identifier #{label}) value: {val})
        ),
        // Value argument without label
        rule!(
            (value_argument value: (_) @val)
            =>
            (argument value: {val})
        ),
        // Navigation expression → member_access_expr
        rule!(
            (navigation_expression target: (_) @target suffix: (navigation_suffix suffix: (_) @member))
            =>
            (member_access_expr target: {target} member: (identifier #{member}))
        ),
        // Return statement
        rule!(
            (control_transfer_statement result: (_) @val)
            =>
            (return_expr value: {val})
        ),
        // Bare return (no value)
        rule!(
            (control_transfer_statement)
            =>
            (return_expr)
        ),
        // Statements block (used inside function bodies and other scopes)
        rule!((statements (_)* @stmts) => (block stmt: {..stmts})),
        // Function body wrapper — unwrap
        rule!((function_body (_) @inner) => {inner}),
        // ---- Closures ----
        // Lambda literal (closure) with body
        rule!(
            (lambda_literal (statements (_)* @body))
            =>
            (function_expr body: (block stmt: {..body}))
        ),
        // Lambda parameter
        rule!(
            (lambda_parameter external_name: (_) @ext name: (_) @name)
            =>
            (parameter
                external_name: (identifier #{ext})
                pattern: (name_pattern identifier: (identifier #{name})))
        ),
        rule!(
            (lambda_parameter name: (_) @name)
            =>
            (parameter pattern: (name_pattern identifier: (identifier #{name})))
        ),
        // Lambda function type — unwrap; just let children translate individually
        rule!((lambda_function_type) => (unsupported_node)),
        rule!((lambda_function_type_parameters) => (unsupported_node)),
        // Call expression with trailing closure (no value_arguments)
        rule!(
            (call_expression (_) @func (call_suffix (lambda_literal (statements (_)* @body))))
            =>
            (call_expr
                function: {func}
                argument: (argument value: (function_expr body: (block stmt: {..body}))))
        ),
        // ---- Fallbacks ----
        rule!(
            (_)
            =>
            (unsupported_node)
        ),
        rule!(
            _ @node
            =>
            {node}
        ),
    ]
}

pub fn language_spec(desugared_ast_schema: &'static str) -> simple::LanguageSpec {
    let desugar = DesugaringConfig::new()
        .add_phase("translate", PhaseKind::OneShot, translation_rules())
        .with_output_node_types_yaml(desugared_ast_schema);
    simple::LanguageSpec {
        prefix: "swift",
        ts_language: tree_sitter_swift::LANGUAGE.into(),
        node_types: tree_sitter_swift::NODE_TYPES,
        file_globs: vec!["*.swift".into(), "*.swiftinterface".into()],
        desugar: Some(desugar),
    }
}
