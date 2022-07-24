const testlib = require('testlib');
const fs = require("fs"),
    fse = require("fs-extra"),
    base64 = require("base-64");

testlib.readFile(function (f) {
    return new Promise((res, rej) => {
        fs.readFile(f, (err, data) => {
            if (err)
                rej(err);
            else
                res(data); /* def=moduleImport("testlib").getMember("readFile").getParameter(0).getReturn().getPromised() */
        });
    });
});

testlib.readFileAndEncode(function (f) {
    return fse.readFile(f)
        .then((data) => /* use=moduleImport("fs-extra").getMember("readFile").getReturn().getPromised() */
            base64.encode(data) /* def=moduleImport("testlib").getMember("readFileAndEncode").getParameter(0).getReturn().getPromised() */
        );
});
