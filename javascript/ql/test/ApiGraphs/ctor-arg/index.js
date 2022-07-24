const testlib = require('testlib');

export class A {
    constructor(x) { /* use=moduleImport("testlib").getParameter(0).getMember("A").getParameter(0) */
        console.log(x);
    }
}

testlib({ A });
