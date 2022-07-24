const testlib = require('testlib');
const impl = require("./lib/impl.js");

testlib({
    impl,
    util: require("./lib/utils"),
    other: require("./lib/stuff"),
    util2: require("./lib/utils2")
});
