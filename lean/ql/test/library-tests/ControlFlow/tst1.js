function t1() {
    source("t1");
    sink(); // $ dominatedBy=t1
}

function t2(x) {
    source("t2.1");
    if (x) {
        source("t2.2");
        sink(); // $ dominatedBy=t2.1 dominatedBy=t2.2
    } else {
        source("t2.3");
        sink(); // $ dominatedBy=t2.1 dominatedBy=t2.3
    }
    sink(); // $ dominatedBy=t2.1 reachedBy=t2.2 reachedBy=t2.3
}

function t3(x) {
    if (source("t3.1") && source("t3.2")) {
        sink() // $ dominatedBy=t3.1-true dominatedBy=t3.2-true
    } else {
        sink(); // $ dominatedBy=t3.1 reachedBy=t3.2-false
    }
}

function t4(x) {
    if (source("t4.1") || source("t4.2")) {
        sink() // $ dominatedBy=t4.1 reachedBy=t4.2-true
    } else {
        sink(); // $ dominatedBy=t4.1-false dominatedBy=t4.2-false
    }
}

function t5(x) {
    if (!(source("t5.1") && source("t5.2"))) {
        sink() // $ dominatedBy=t5.1 reachedBy=t5.2-false
    } else {
        sink(); // $ dominatedBy=t5.1-true dominatedBy=t5.2-true
    }
}

function t6(x) {
    if (!(source("t6.1") || source("t6.2"))) {
        sink() // $ dominatedBy=t6.1-false dominatedBy=t6.2-false
    } else {
        sink(); // $ dominatedBy=t6.1 reachedBy=t6.2-true
    }
}

function t7(x) {
    // Complex nested AND-OR combination
    if ((source("t7.1") && source("t7.2")) || source("t7.3")) {
        sink() // $ dominatedBy=t7.1 reachedBy=t7.3-true reachedBy=t7.2
    } else {
        sink(); // $ dominatedBy=t7.3-false dominatedBy=t7.1 reachedBy=t7.2-false
    }
}

function t8(x) {
    // Complex nested OR-AND combination
    if ((source("t8.1") || source("t8.2")) && source("t8.3")) {
        sink() // $ dominatedBy=t8.1 reachedBy=t8.2-true dominatedBy=t8.3-true
    } else {
        sink(); // $ dominatedBy=t8.1 reachedBy=t8.2 reachedBy=t8.3-false
    }
}

function t9(x) {
    // Triple AND combination
    if (source("t9.1") && source("t9.2") && source("t9.3")) {
        sink() // $ dominatedBy=t9.1-true dominatedBy=t9.2-true dominatedBy=t9.3-true
    } else {
        sink(); // $ dominatedBy=t9.1 reachedBy=t9.3-false reachedBy=t9.2
    }
}

function t10(x) {
    // Triple OR combination
    if (source("t10.1") || source("t10.2") || source("t10.3")) {
        sink() // $ dominatedBy=t10.1 reachedBy=t10.3-true reachedBy=t10.2
    } else {
        sink(); // $ dominatedBy=t10.1-false dominatedBy=t10.2-false dominatedBy=t10.3-false
    }
}

function t11(x) {
    // Nested NOT with AND-OR
    if (!(source("t11.1") && (source("t11.2") || source("t11.3")))) {
        sink() // $ dominatedBy=t11.1 reachedBy=t11.2-false reachedBy=t11.3-false
    } else {
        sink(); // $ dominatedBy=t11.1-true dominatedBy=t11.2 reachedBy=t11.3-true
    }
}

function t12(x) {
    // Nested NOT with OR-AND
    if (!(source("t12.1") || (source("t12.2") && source("t12.3")))) {
        sink() // $ dominatedBy=t12.1-false dominatedBy=t12.2 reachedBy=t12.3-false
    } else {
        sink(); // $ dominatedBy=t12.1 reachedBy=t12.2-true reachedBy=t12.3-true
    }
}

function t13(x) {
    // Deeply nested combination (AND-OR-AND)
    if (source("t13.1") && (source("t13.2") || (source("t13.3") && source("t13.4")))) {
        sink() // $ dominatedBy=t13.1-true dominatedBy=t13.2 reachedBy=t13.3-true reachedBy=t13.4-true
    } else {
        sink(); // $ dominatedBy=t13.1 reachedBy=t13.2-false reachedBy=t13.3 reachedBy=t13.4-false
    }
}

function t14(x) {
    // Deeply nested combination (OR-AND-OR)
    if (source("t14.1") || (source("t14.2") && (source("t14.3") || source("t14.4")))) {
        sink() // $ dominatedBy=t14.1 reachedBy=t14.2-true reachedBy=t14.3 reachedBy=t14.4-true
    } else {
        sink(); // $ dominatedBy=t14.1-false dominatedBy=t14.2 reachedBy=t14.3-false reachedBy=t14.4-false
    }
}

function t15(x) {
    // NOT with triple nested operators
    if (!(source("t15.1") && source("t15.2") && source("t15.3"))) {
        sink() // $ dominatedBy=t15.1 reachedBy=t15.3-false reachedBy=t15.2
    } else {
        sink(); // $ dominatedBy=t15.1-true dominatedBy=t15.2-true dominatedBy=t15.3-true
    }
}

function t16(x) {
    // Combined ternary and logical operators
    if (source("t16.1") ? (source("t16.2") && source("t16.3")) : source("t16.4")) {
        sink() // $ dominatedBy=t16.1 reachedBy=t16.2-true reachedBy=t16.3-true reachedBy=t16.4-true
    } else {
        sink(); // $ dominatedBy=t16.1 reachedBy=t16.2 reachedBy=t16.3-false reachedBy=t16.4-false
    }
}

function t17(x) {
    // Multiple levels of nesting with mixed operators (AND-OR-AND-OR)
    if (source("t17.1") && ((source("t17.2") || source("t17.3")) && (source("t17.4") || source("t17.5")))) {
        sink() // $ dominatedBy=t17.1-true dominatedBy=t17.2 reachedBy=t17.3-true dominatedBy=t17.4 reachedBy=t17.5-true
    } else {
        sink(); // $ dominatedBy=t17.1 reachedBy=t17.4-false reachedBy=t17.5-false reachedBy=t17.2 reachedBy=t17.3
    }
}

function t18(x) {
    // Triple NOT with complex nesting
    if (!!!(source("t18.1") || source("t18.2"))) {
        sink() // $ dominatedBy=t18.1-false dominatedBy=t18.2-false
    } else {
        sink(); // $ dominatedBy=t18.1 reachedBy=t18.2-true
    }
}

function t19(x) {
    // Alternating AND-OR chain
    if (source("t19.1") && source("t19.2") || source("t19.3") && source("t19.4")) {
        sink() // $ dominatedBy=t19.1 reachedBy=t19.2 reachedBy=t19.3-true reachedBy=t19.4-true
    } else {
        sink(); // $ dominatedBy=t19.1 reachedBy=t19.2-false dominatedBy=t19.3 reachedBy=t19.4-false
    }
}

function t20(x) {
    // Multiple negations with complex expressions
    if (!(!source("t20.1") || !source("t20.2"))) {
        sink() // $ dominatedBy=t20.1-true dominatedBy=t20.2-true
    } else {
        sink(); // $ dominatedBy=t20.1 reachedBy=t20.2-false
    }
}

function t21(x) {
    // Deeply nested combination with multiple operators
    if ((source("t21.1") || (source("t21.2") && source("t21.3"))) &&
        (source("t21.4") || (source("t21.5") && (source("t21.6") || source("t21.7"))))) {
        sink() // $ dominatedBy=t21.1 reachedBy=t21.2-true reachedBy=t21.3-true dominatedBy=t21.4 reachedBy=t21.5-true reachedBy=t21.7-true reachedBy=t21.6
    } else {
        sink(); // $ dominatedBy=t21.1 reachedBy=t21.2 reachedBy=t21.3 reachedBy=t21.4-false reachedBy=t21.5 reachedBy=t21.6-false reachedBy=t21.7-false
    }
}

function t22(x) {
    // NOT with deeply nested AND-OR-AND
    if (!(source("t22.1") && (source("t22.2") || (source("t22.3") && source("t22.4"))))) {
        sink() // $ dominatedBy=t22.1 reachedBy=t22.2-false reachedBy=t22.4-false reachedBy=t22.3
    } else {
        sink(); // $ dominatedBy=t22.1-true reachedBy=t22.3-true reachedBy=t22.4-true dominatedBy=t22.2
    }
}

function t23(x) {
    // Cascading ternary with logical operators
    if (source("t23.1") ?
                 source("t23.2") && source("t23.3") :
                 source("t23.4") || source("t23.5")) {
        sink() // $ dominatedBy=t23.1 reachedBy=t23.2-true reachedBy=t23.3-true reachedBy=t23.4 reachedBy=t23.5-true
    } else {
        sink(); // $ dominatedBy=t23.1 reachedBy=t23.2 reachedBy=t23.3-false reachedBy=t23.4-false reachedBy=t23.5-false
    }
}

function t25(x) {
    // Four-level deep combination (OR-AND-OR-AND)
    if (source("t25.1") || (source("t25.2") && (source("t25.3") || (source("t25.4") && source("t25.5"))))) {
        sink() // $ dominatedBy=t25.1 reachedBy=t25.2-true reachedBy=t25.4-true reachedBy=t25.5-true reachedBy=t25.3
    } else {
        sink(); // $ dominatedBy=t25.1-false dominatedBy=t25.2 reachedBy=t25.3-false reachedBy=t25.4 reachedBy=t25.5-false
    }
}

function t27(x) {
    // Complex expressions with multiple NOTs and parentheses
    if (!(!(source("t27.1") || !(source("t27.2") && source("t27.3"))))) {
        sink() // $ dominatedBy=t27.1 reachedBy=t27.2 reachedBy=t27.3-false
    } else {
        sink(); // $ dominatedBy=t27.1-false dominatedBy=t27.2-true dominatedBy=t27.3-true
    }
}

function t31(x) {
    // Multi-level negation with logical operators
    if (!!(!(source("t31.1") || source("t31.2")) || !(source("t31.3") && source("t31.4")))) {
        sink() // $ reachedBy=t31.3 reachedBy=t31.4-false dominatedBy=t31.1 reachedBy=t31.2
    } else {
        sink(); // $ dominatedBy=t31.1 reachedBy=t31.2-true dominatedBy=t31.3-true dominatedBy=t31.4-true
    }
}

function t32(x) {
    // Five-level deep nesting with combined operators
    if (source("t32.1") && (
        source("t32.2") || (
            source("t32.3") && (
                source("t32.4") || (
                    source("t32.5") && source("t32.6")
                )
            )
        )
    )) {
        sink() // $ dominatedBy=t32.1-true reachedBy=t32.3-true reachedBy=t32.5-true reachedBy=t32.6-true dominatedBy=t32.2 reachedBy=t32.4
    } else {
        sink(); // $ dominatedBy=t32.1 reachedBy=t32.2-false reachedBy=t32.4-false reachedBy=t32.6-false reachedBy=t32.3 reachedBy=t32.5
    }
}
