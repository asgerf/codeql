const assert = require("assert");

let o = {
    foo: 23 // def=moduleImport("assert").getMember("equal").getParameter(0).getMember("foo")
};
assert.equal(o, o);
