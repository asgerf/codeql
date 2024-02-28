define('amd-named-modules/lib', [], function () {
    return {
        foo: {
            baz: 123 // def=moduleImport("amd-named-modules").getMember("exports").getMember("bar").getMember("baz")
        }
    };
});

define('amd-named-modules', ['amd-named-modules/lib'], function(foo) {
    return {
        bar: foo.foo // def=moduleImport("amd-named-modules").getMember("exports").getMember("bar")
    }
});
