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
        // A referenceable_operator (e.g. `+` used as a value, as in `reduce(0, +)`)
        // is treated as a name reference to the operator symbol.
        rule!((referenceable_operator) @op => (name_expr identifier: (identifier #{op}))),
        // ---- Operators ----
        // All binary operators share the lhs/op/rhs shape.
        rule!((additive_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((multiplicative_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((comparison_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((equality_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((conjunction_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((disjunction_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        rule!((infix_expression lhs: (_) @l op: _ @op rhs: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        // Range expression `a..<b` / `a...b`
        rule!((range_expression start: (_) @l op: _ @op end: (_) @r) => (binary_expr left: {l} operator: (operator #{op}) right: {r})),
        // Open-ended ranges `a...` / `...b`
        rule!((open_end_range_expression start: (_) @l) => (unary_expr operator: (operator "...") operand: {l})),
        rule!((open_start_range_expression end: (_) @r) => (unary_expr operator: (operator "...") operand: {r})),
        // Custom operator declaration: `[prefix|infix|postfix] operator OP [: PrecedenceGroup]`.
        // The fixity keyword is an anonymous child of `operator_declaration`, so we
        // dispatch on it with one rule per keyword.
        rule!(
            (operator_declaration "prefix" (referenceable_operator (_) @op) (simple_identifier)? @prec)
            =>
            (operator_syntax_declaration name: (identifier #{op}) fixity: (fixity "prefix") precedence: {..prec})
        ),
        rule!(
            (operator_declaration "postfix" (referenceable_operator (_) @op) (simple_identifier)? @prec)
            =>
            (operator_syntax_declaration name: (identifier #{op}) fixity: (fixity "postfix") precedence: {..prec})
        ),
        rule!(
            (operator_declaration "infix" (referenceable_operator (_) @op) (simple_identifier)? @prec)
            =>
            (operator_syntax_declaration
                name: (identifier #{op})
                fixity: (fixity "infix")
                precedence: {..prec})
        ),
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
        // Computed property with just a body (shorthand getter) — must be before general accessor rule
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (pattern bound_identifier: (_) @name)
                computed_value: (computed_property (statements (_)* @body)))
            =>
            (computed_property_declaration
                modifier: (modifier #{binding_kind})
                name: (identifier #{name})
                accessors: (computed_property_accessor
                    accessor_kind: (accessor_kind "get")
                    body: (block stmt: {..body})))
        ),
        // Computed property (with accessors via computed_value field)
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (pattern bound_identifier: (_) @name)
                computed_value: (computed_property (_)* @accessors))
            =>
            (computed_property_declaration
                modifier: (modifier #{binding_kind})
                name: (identifier #{name})
                accessors: {..accessors})
        ),
        // Property with willSet/didSet observers (initializer optional).
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (pattern bound_identifier: (_) @name)
                value: (_)? @val
                (willset_didset_block (_)* @observers))
            =>
            (computed_property_declaration
                modifier: (modifier #{binding_kind})
                name: (identifier #{name})
                initializer: {..val}
                accessors: {..observers})
        ),
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
        // Property declaration (let/var binding) with simple identifier pattern;
        // value is optional (type-only declaration).
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (pattern bound_identifier: (_) @name)
                value: (_)? @val)
            =>
            (variable_declaration
                modifier: (modifier #{binding_kind})
                pattern: (name_pattern identifier: (identifier #{name}))
                value: {..val})
        ),
        // Property declaration with a complex pattern (tuple destructuring etc.);
        // value optional.
        rule!(
            (property_declaration
                (value_binding_pattern mutability: _ @binding_kind)
                name: (_) @pat
                value: (_)? @val)
            =>
            (variable_declaration
                modifier: (modifier #{binding_kind})
                pattern: {pat}
                value: {..val})
        ),
        // Unwrap `type` wrapper node
        rule!((type name: (_) @inner) => {inner}),
        // `directly_assignable_expression` is just a wrapper; unwrap it
        rule!((directly_assignable_expression (_) @inner) => {inner}),
        // Pattern with bound_identifier → name_pattern
        rule!((pattern bound_identifier: (_) @name) => (name_pattern identifier: (identifier #{name}))),
        // Tuple pattern (destructuring)
        rule!((pattern (pattern)* @elems) => (tuple_pattern element: {..elems})),
        // ---- Functions ----
        // Function declaration
        // Function declaration (return type optional, body statements optional).
        rule!(
            (function_declaration
                name: (_) @name
                (parameter)* @params
                return_type: (_)? @ret
                body: (function_body (statements (_)* @body_stmts)?))
            =>
            (function_declaration
                name: (identifier #{name})
                parameter: {..params}
                return_type: {..ret}
                body: (block stmt: {..body_stmts}))
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
        // Value argument with reference_specifier label (some argument labels use this field)
        rule!(
            (value_argument reference_specifier: (value_argument_label (_) @label))
            =>
            (argument name: (identifier #{label}))
        ),
        // Navigation expression → member_access_expr
        rule!(
            (navigation_expression target: (_) @target suffix: (navigation_suffix suffix: (_) @member))
            =>
            (member_access_expr target: {target} member: (identifier #{member}))
        ),
        // Return / break / continue, one rule per keyword.
        // The anonymous "return"/"break"/"continue" keywords are matched as
        // string literals.
        rule!((control_transfer_statement "return" result: (_)? @val) => (return_expr value: {..val})),
        rule!((control_transfer_statement "break" result: (_) @lbl) => (break_expr label: (identifier #{lbl}))),
        rule!((control_transfer_statement "break") => (break_expr)),
        rule!((control_transfer_statement "continue" result: (_) @lbl) => (continue_expr label: (identifier #{lbl}))),
        rule!((control_transfer_statement "continue") => (continue_expr)),
        // throw_statement → throw_expr (unwrap the keyword, keep the expression).
        rule!((throw_statement (throw_keyword) (_) @val) => (throw_expr value: {val})),
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
        // ---- Control flow ----
        // If statement with else clause followed by another statements block
        rule!(
            (if_statement condition: (_) @cond (statements (_)* @then_stmts) (else) (statements (_)* @else_stmts))
            =>
            (if_expr
                condition: {cond}
                then: (block stmt: {..then_stmts})
                else: (block stmt: {..else_stmts}))
        ),
        // If statement with else-if chain
        rule!(
            (if_statement condition: (_) @cond (statements (_)* @then_stmts) (else) (if_statement) @else_if)
            =>
            (if_expr
                condition: {cond}
                then: (block stmt: {..then_stmts})
                else: {else_if})
        ),
        // If statement without else
        rule!(
            (if_statement condition: (_) @cond (statements (_)* @then_stmts))
            =>
            (if_expr
                condition: {cond}
                then: (block stmt: {..then_stmts}))
        ),
        // Guard statement
        rule!(
            (guard_statement condition: (_) @cond (else) (statements (_)* @else_stmts))
            =>
            (guard_if_stmt
                condition: {cond}
                else: (block stmt: {..else_stmts}))
        ),
        // Ternary expression → if_expr
        rule!(
            (ternary_expression condition: (_) @cond if_true: (_) @then_val if_false: (_) @else_val)
            =>
            (if_expr condition: {cond} then: {then_val} else: {else_val})
        ),
        // Switch statement
        rule!(
            (switch_statement expr: (_) @val (switch_entry)* @cases)
            =>
            (switch_expr value: {val} case: {..cases})
        ),
        // Switch entry with patterns and body
        rule!(
            (switch_entry (switch_pattern)* @pats (statements (_)* @body))
            =>
            (switch_case pattern: {..pats} body: (block stmt: {..body}))
        ),
        // Switch entry: default case (no patterns)
        rule!(
            (switch_entry (default_keyword) (statements (_)* @body))
            =>
            (switch_case body: (block stmt: {..body}))
        ),
        // Switch pattern — unwrap to inner pattern
        rule!((switch_pattern (pattern)* @inner) => {..inner}),
        // If-let binding (value optional → shorthand form).
        rule!(
            (if_let_binding (value_binding_pattern mutability: _ @binding_kind) bound_identifier: (_) @name (_)? @val)
            =>
            (pattern_guard_expr
                value: {..val}
                pattern: (name_pattern identifier: (identifier #{name})))
        ),
        // If-condition — unwrap (pass through the inner expression/pattern)
        rule!((if_condition (_) @inner) => {inner}),
        // ---- Loops ----
        // For-in loop with optional where-clause guard.
        rule!(
            (for_statement
                item: (_) @pat
                collection: (_) @iter
                (where_clause (where_keyword) (_) @guard)?
                (statements (_)* @body))
            =>
            (for_each_stmt
                pattern: {pat}
                iterable: {iter}
                guard: {..guard}
                body: (block stmt: {..body}))
        ),
        // While loop
        rule!(
            (while_statement condition: (_) @cond (statements (_)* @body))
            =>
            (while_stmt condition: {cond} body: (block stmt: {..body}))
        ),
        // Repeat-while loop
        rule!(
            (repeat_while_statement condition: (_) @cond (statements (_)* @body))
            =>
            (do_while_stmt condition: {cond} body: (block stmt: {..body}))
        ),
        // Labeled statement (e.g. `outer: for ...`). Strip the trailing ':' from the label token.
        rule!((labeled_statement label: (statement_label) @lbl statement: (_) @stmt) => {..{
            let text = __yeast_ctx.ast.source_text(lbl.into());
            let name = __yeast_ctx.literal("identifier", &text[..text.len() - 1]);
            vec![__yeast_ctx.node("labeled_stmt", vec![("label", vec![name]), ("stmt", vec![stmt.into()])])]
        }}),
        // ---- Collections ----
        // Array literal
        rule!((array_literal element: (_)* @elems) => (array_literal element: {..elems})),
        // Empty array literal
        rule!((array_literal) => (array_literal)),
        // Dictionary literal — zip keys and values into key_value_pairs
        rule!(
            (dictionary_literal key: (_)* @keys value: (_)* @vals)
            =>
            (map_literal element: {..{
                keys.iter().zip(vals.iter()).map(|(&k, &v)| {
                    let k_id: usize = k.into();
                    let v_id: usize = v.into();
                    __yeast_ctx.node("key_value_pair", vec![
                        ("key", vec![k_id]),
                        ("value", vec![v_id]),
                    ])
                }).collect::<Vec<_>>()
            }})
        ),
        // ---- Optionals and errors ----
        // Optional chaining — unwrap the marker
        rule!((optional_chain_marker (_) @inner) => {inner}),
        // try/try?/try! expr → unary_expr with operator "try", "try?" or "try!"
        rule!((try_expression (try_operator) @op expr: (_) @inner) => (unary_expr operator: (operator #{op}) operand: {inner})),
        // Do-catch → try_expr
        rule!(
            (do_statement (statements (_)* @body) (catch_block)* @catches)
            =>
            (try_expr
                body: (block stmt: {..body})
                catch_clause: {..catches})
        ),
        // Catch block with bound identifier; optional where-clause guard.
        rule!(
            (catch_block (catch_keyword)
                error: (pattern bound_identifier: (_) @name)
                (where_clause (where_keyword) (_) @guard)?
                (statements (_)* @body))
            =>
            (catch_clause
                pattern: (name_pattern identifier: (identifier #{name}))
                guard: {..guard}
                body: (block stmt: {..body}))
        ),
        // Catch block without error binding
        rule!(
            (catch_block (catch_keyword) (statements (_)* @body))
            =>
            (catch_clause body: (block stmt: {..body}))
        ),
        // Catch block with unhandled pattern — preserve pattern; optional body.
        rule!(
            (catch_block (catch_keyword) error: (_) @pat (statements (_)* @body)?)
            =>
            (catch_clause
                pattern: {pat}
                body: (block stmt: {..body}))
        ),
        // As expression (type cast) — as?, as!
        rule!((as_expression (as_operator) @op expr: (_) @val type: (_) @ty) => (type_cast_expr expr: {val} operator: (operator #{op}) type: {ty})),
        // Check expression (`x is T`) → type_test_expr
        rule!((check_expression op: _ @op target: (_) @val type: (_) @ty) => (type_test_expr expr: {val} operator: (operator #{op}) type: {ty})),
        // Await expression → unary_expr with operator "await"
        rule!((await_expression expr: (_) @val) => (unary_expr operator: (operator "await") operand: {val})),
        rule!((await_expression (_) @val) => (unary_expr operator: (operator "await") operand: {val})),
        // Import declaration → import_declaration with path identifiers
        rule!(
            (import_declaration (identifier (simple_identifier)* @parts) (modifiers)* @mods)
            =>
            {..{
                let path: Vec<usize> = parts.iter().map(|&p| {
                    let text = __yeast_ctx.ast.source_text(p.into());
                    __yeast_ctx.literal("identifier", &text)
                }).collect();
                let mod_ids: Vec<usize> = mods.iter().map(|&m| m.into()).collect();
                let mut fields: Vec<(&str, Vec<usize>)> = vec![("path", path)];
                if !mod_ids.is_empty() {
                    fields.push(("modifier", mod_ids));
                }
                vec![__yeast_ctx.node("import_declaration", fields)]
            }}
        ),
        // ---- Types and classes ----
        // Self expression → keyword_literal
        rule!((self_expression) => (keyword_literal)),
        // Super expression → super_expr
        rule!((super_expression) => (super_expr)),
        // Modifiers — unwrap to individual modifier children
        rule!((modifiers (_)* @mods) => {..mods}),
        rule!((visibility_modifier) @m => (modifier #{m})),
        rule!((function_modifier) @m => (modifier #{m})),
        rule!((member_modifier) @m => (modifier #{m})),
        rule!((mutation_modifier) @m => (modifier #{m})),
        rule!((ownership_modifier) @m => (modifier #{m})),
        rule!((property_modifier) @m => (modifier #{m})),
        rule!((parameter_modifier) @m => (modifier #{m})),
        rule!((inheritance_modifier) @m => (modifier #{m})),
        rule!((property_behavior_modifier) @m => (modifier #{m})),
        // Type annotations — unwrap
        rule!((type_annotation (_) @inner) => {inner}),
        // User type → named_type_expr (single or qualified component)
        rule!((user_type (type_identifier)+ @parts) => {..{
            let mut acc: Option<usize> = None;
            for p in parts.iter() {
                let text = __yeast_ctx.ast.source_text((*p).into());
                let name_node = __yeast_ctx.literal("identifier", &text);
                acc = Some(match acc {
                    None => __yeast_ctx.node("named_type_expr", vec![("name", vec![name_node])]),
                    Some(qual) => __yeast_ctx.node("named_type_expr", vec![
                        ("qualifier", vec![qual]),
                        ("name", vec![name_node]),
                    ]),
                });
            }
            acc.into_iter().collect::<Vec<_>>()
        }}),
        // Tuple type → tuple_type_expr
        rule!((tuple_type element: (_)* @elems) => (tuple_type_expr element: {..elems})),
        rule!((tuple_type_item name: (_) @name type: (_) @ty) => (tuple_type_element name: (identifier #{name}) type: {ty})),
        rule!((tuple_type_item type: (_) @ty) => (tuple_type_element type: {ty})),
        // Array type `[T]` → generic_type_expr with Array base
        rule!((array_type element: (_) @e) => (generic_type_expr
            base: (named_type_expr name: (identifier "Array"))
            type_argument: {e})),
        // Dictionary type `[K: V]` → generic_type_expr with Dictionary base
        rule!((dictionary_type key: (_) @k value: (_) @v) => (generic_type_expr
            base: (named_type_expr name: (identifier "Dictionary"))
            type_argument: {k}
            type_argument: {v})),
        // Optional type `T?` → generic_type_expr with Optional base
        rule!((optional_type wrapped: (_) @w) => (generic_type_expr
            base: (named_type_expr name: (identifier "Optional"))
            type_argument: {w})),
        // Function type `(Params) -> Ret` → function_type_expr.
        rule!((function_type parameter: (_)* @ps return_type: (_) @ret) => (function_type_expr parameter: {..ps} return_type: {ret})),
        rule!((function_type_parameter name: (_) @name type: (_) @ty) => (parameter external_name: (identifier #{name}) type: {ty})),
        rule!((function_type_parameter type: (_) @ty) => (parameter type: {ty})),
        // Selector expression: `#selector(inner)` → call_expr of `#selector` with one argument
        rule!(
            (selector_expression (_) @inner)
            =>
            (call_expr
                function: (name_expr identifier: (identifier "#selector"))
                argument: (argument value: {inner}))
        ),
        // Key path expression: `\Person.name` parses as a navigation_expression
        // whose target is `key_path_expression` containing a type_identifier.
        // Translate the key-path leader to a name_expr containing the literal
        // source text (e.g. `\Person`) so the surrounding member access still
        // works.
        rule!((key_path_expression) @kp => (name_expr identifier: (identifier #{kp}))),
        // Inheritance specifier → base_type
        rule!((inheritance_specifier inherits_from: (_) @ty) => {..{
            let ty_id: usize = ty.into();
            vec![__yeast_ctx.node("base_type", vec![("type", vec![ty_id])])]
        }}),
        // User type with multiple components (qualified) → nested named_type_expr
        rule!((user_type (type_identifier)* @parts (type_arguments (_)* @args))
            => (generic_type_expr
                base: {..{
                    let result = parts.iter().copied().fold(None, |acc: Option<usize>, part| {
                        let text = __yeast_ctx.ast.source_text(part.into());
                        let name_node = __yeast_ctx.literal("identifier", &text);
                        Some(if let Some(qual) = acc {
                            __yeast_ctx.node("named_type_expr", vec![
                                ("qualifier", vec![qual]),
                                ("name", vec![name_node]),
                            ])
                        } else {
                            __yeast_ctx.node("named_type_expr", vec![
                                ("name", vec![name_node]),
                            ])
                        })
                    });
                    result.into_iter().collect::<Vec<_>>()
                }}
                type_argument: {..args})),
        // Class declaration with body containing members
        rule!(
            (class_declaration
                declaration_kind: _ @kind
                name: (_) @name
                body: (class_body (_)* @members)
                (inheritance_specifier)* @bases
                (modifiers)* @mods)
            =>
            (class_like_declaration
                modifier: (modifier #{kind})
                modifier: {..mods}
                name: (identifier #{name})
                base_type: {..bases}
                member: {..members})
        ),
        // Class declaration with enum body
        rule!(
            (class_declaration
                declaration_kind: _ @kind
                name: (_) @name
                body: (enum_class_body (_)* @members)
                (inheritance_specifier)* @bases
                (modifiers)* @mods)
            =>
            (class_like_declaration
                modifier: (modifier #{kind})
                modifier: {..mods}
                name: (identifier #{name})
                base_type: {..bases}
                member: {..members})
        ),
        // Class declaration with empty body
        rule!(
            (class_declaration
                declaration_kind: _ @kind
                name: (_) @name
                body: (_)
                (inheritance_specifier)* @bases
                (modifiers)* @mods)
            =>
            (class_like_declaration
                modifier: (modifier #{kind})
                modifier: {..mods}
                name: (identifier #{name})
                base_type: {..bases})
        ),
        // Protocol declaration
        rule!(
            (protocol_declaration
                declaration_kind: _ @kind
                name: (_) @name
                body: (protocol_body (_)* @members)
                (inheritance_specifier)* @bases
                (modifiers)* @mods)
            =>
            (class_like_declaration
                modifier: (modifier #{kind})
                modifier: {..mods}
                name: (identifier #{name})
                base_type: {..bases}
                member: {..members})
        ),
        // Protocol function — return type and body statements both optional.
        rule!(
            (protocol_function_declaration
                name: (_) @name
                (parameter)* @params
                return_type: (_)? @ret
                body: (function_body (statements (_)* @body_stmts)?)?
                (modifiers)* @mods)
            =>
            (function_declaration
                modifier: {..mods}
                name: (identifier #{name})
                parameter: {..params}
                return_type: {..ret}
                body: (block stmt: {..body_stmts}))
        ),
        // Protocol property → computed_property_declaration
        rule!(
            (protocol_property_declaration
                name: (pattern bound_identifier: (_) @name)
                (protocol_property_requirements)* @_reqs
                (modifiers)* @mods)
            =>
            (computed_property_declaration
                modifier: {..mods}
                name: (identifier #{name}))
        ),
        // Init declaration → constructor_declaration. Body statements optional;
        // body itself is also optional (protocol requirement).
        rule!(
            (init_declaration
                (parameter)* @params
                body: (function_body (statements (_)* @body_stmts)?)?
                (modifiers)* @mods)
            =>
            (constructor_declaration
                modifier: {..mods}
                parameter: {..params}
                body: (block stmt: {..body_stmts}))
        ),
        // Deinit declaration → destructor_declaration. Body statements optional.
        rule!(
            (deinit_declaration
                body: (function_body (statements (_)* @body_stmts)?)
                (modifiers)* @mods)
            =>
            (destructor_declaration
                modifier: {..mods}
                body: (block stmt: {..body_stmts}))
        ),
        // Enum case group → flatten cases
        rule!(
            (enum_case_group case: (_)* @cases)
            =>
            {..cases}
        ),
        // Enum data content → parameter
        rule!(
            (enum_data_content external_name: (_) @ext name: (_) @int type: (_) @ty)
            =>
            (parameter
                external_name: (identifier #{ext})
                pattern: (name_pattern identifier: (identifier #{int}))
                type: {ty})
        ),
        rule!(
            (enum_data_content external_name: (_) @ext type: (_) @ty)
            =>
            (parameter
                external_name: (identifier #{ext})
                type: {ty})
        ),
        rule!(
            (enum_data_content name: (_) @n type: (_) @ty)
            =>
            (parameter
                external_name: (identifier #{n})
                type: {ty})
        ),
        rule!(
            (enum_data_content type: (_) @ty)
            =>
            (parameter
                type: {ty})
        ),
        // Enum struct case → class_like_declaration with constructor
        rule!(
            (enum_struct_case name: (_) @name data_content: (_)* @params)
            =>
            (class_like_declaration
                modifier: (modifier "enum_case")
                name: (identifier #{name})
                member: (constructor_declaration
                    parameter: {..params}
                    body: (block)))
        ),
        // Enum scalar case → variable_declaration
        rule!(
            (enum_scalar_case name: (_) @name)
            =>
            (variable_declaration
                modifier: (modifier "enum_case")
                pattern: (name_pattern
                    identifier: (identifier #{name})))
        ),
        // Typealias declaration — uses code block to work around `type` keyword issue in macro
        rule!(
            (typealias_declaration name: (_) @name value: (_) @val (modifiers)* @mods)
            =>
            {..{
                let name_text = __yeast_ctx.ast.source_text(name.into());
                let ident = __yeast_ctx.literal("identifier", &name_text);
                let val_id: usize = val.into();
                let mut fields = vec![
                    ("name", vec![ident]),
                    ("type", vec![val_id]),
                ];
                let mod_ids: Vec<usize> = mods.iter().map(|&m| m.into()).collect();
                if !mod_ids.is_empty() {
                    fields.push(("modifier", mod_ids));
                }
                vec![__yeast_ctx.node("type_alias_declaration", fields)]
            }}
        ),
        // Subscript declaration (treat as function for now)
        rule!(
            (subscript_declaration (parameter)* @params (modifiers)* @mods)
            =>
            (function_declaration
                modifier: {..mods}
                name: (identifier "subscript")
                parameter: {..params}
                body: (block))
        ),
        // Associated type declaration (with optional bound)
        rule!(
            (associatedtype_declaration name: (_) @name inherits_from: (_)? @bound (modifiers)* @mods)
            =>
            (associated_type_declaration
                modifier: {..mods}
                name: (identifier #{name})
                bound: {..bound})
        ),
        // Protocol property requirements — just discard
        rule!((protocol_property_requirements) => (unsupported_node)),
        // Computed getter → computed_property_accessor (body optional).
        rule!(
            (computed_getter (getter_specifier) (statements (_)* @body)?)
            =>
            (computed_property_accessor
                accessor_kind: (accessor_kind "get")
                body: (block stmt: {..body}))
        ),
        // Computed setter with explicit parameter name.
        rule!(
            (computed_setter (setter_specifier) (_) @param (statements (_)* @body))
            =>
            (computed_property_accessor
                accessor_kind: (accessor_kind "set")
                parameter: (parameter pattern: (name_pattern identifier: (identifier #{param})))
                body: (block stmt: {..body}))
        ),
        // Computed setter without explicit parameter name; body optional.
        rule!(
            (computed_setter (setter_specifier) (statements (_)* @body)?)
            =>
            (computed_property_accessor
                accessor_kind: (accessor_kind "set")
                body: (block stmt: {..body}))
        ),
        // Computed modify → computed_property_accessor
        rule!(
            (computed_modify (modify_specifier) (statements (_)* @body))
            =>
            (computed_property_accessor
                accessor_kind: (accessor_kind "modify")
                body: (block stmt: {..body}))
        ),
        // willset/didset block — spread to children
        rule!((willset_didset_block (_)* @clauses) => {..clauses}),
        // willset clause → computed_property_accessor (body optional).
        rule!(
            (willset_clause (statements (_)* @body)?)
            =>
            (computed_property_accessor
                accessor_kind: (accessor_kind "willSet")
                body: (block stmt: {..body}))
        ),
        // didset clause → computed_property_accessor (body optional).
        rule!(
            (didset_clause (statements (_)* @body)?)
            =>
            (computed_property_accessor
                accessor_kind: (accessor_kind "didSet")
                body: (block stmt: {..body}))
        ),
        // Preprocessor conditionals — unsupported
        rule!((diagnostic) => (unsupported_node)),
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
