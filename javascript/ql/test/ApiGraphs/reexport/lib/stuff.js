function foo(x) { /* use=moduleImport("testlib").getParameter(0).getMember("other").getMember("bar").getParameter(0) */
    return x + 1;
}

export const bar = foo;
