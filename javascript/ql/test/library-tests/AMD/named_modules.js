define('foo', [], function () {
    return {
        foo: 23
    };
});

define('bar', ['foo'], function(foo) {
    return {
        bar: foo.foo
    }
});
