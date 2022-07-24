function foo(x) { /* use=moduleImport("reexport").getMember("other").getMember("bar").getParameter(0) */
    return x + 1;
}

export const bar = foo;
