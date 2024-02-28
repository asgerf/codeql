define('foo', ['exports'], function (exports) {
    /** name:amd.foo */
    exports.foo = function() {};
});

define('bar', ['./foo'], function (foo) {
    /** calls:amd.foo */
    foo.foo();
});
