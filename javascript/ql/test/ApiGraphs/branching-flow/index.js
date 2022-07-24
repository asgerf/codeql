const testlib = require('testlib');

testlib.foo(function (cb) {
    if (!cb)
        cb = function () { };
    cb(fs.readFileSync("/etc/passwd")); /* use=moduleImport("testlib").getMember("foo").getParameter(0).getParameter(0) */
});
