const testlib = require('testlib');

const myExports = {};

myExports.foo = function (x) { /* use=moduleImport("testlib").getParameter(0).getMember("foo").getParameter(0) */
    return x;
};

myExports.foo.bar = function (y) { /* MISSING: use=moduleImport("testlib").getParameter(0).getMember("foo").getMember("bar").getParameter(0) */
    return y;
};

testlib(myExports);

testlib({
    foo2: {
        bar2: function(x) {} /* use=moduleImport("testlib").getParameter(0).getMember("foo2").getMember("bar2").getParameter(0) */
    }
});
