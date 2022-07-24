const testlib = require('testlib');

export class A {
    foo() {
        return this; /* def=moduleImport("testlib").getParameter(0).getMember("A").getInstance().getMember("foo").getReturn() */
    }
    bar(x) { } /* use=moduleImport("testlib").getParameter(0).getMember("A").getInstance().getMember("bar").getParameter(0) */
}

testlib({ A });
