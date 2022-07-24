const fs = require('fs');

exports.foo = function (cb) {
    if (!cb)
        cb = function () { };
    cb(fs.readFileSync("/etc/passwd")); /* def=moduleImport("branching-flow").getMember("foo").getParameter(0).getParameter(0) */
};
