const testlib = require('testlib');

function assertNotNull(x) {
    if (x === null)
        throw new TypeError();
}

testlib.foo(function(x) {
    assertNotNull(x);
    sink(x.f); /* use=moduleImport("testlib").getMember("foo").getParameter(0).getParameter(0).getMember("f") */
});
