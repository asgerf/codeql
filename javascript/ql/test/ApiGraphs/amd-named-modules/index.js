define('amd-named-modules/lib', [], function () {
    return {
        foo: {
            baz: 123 // def=moduleImport("amd-named-modules").getMember("exports").getMember("bar").getMember("baz")
        }
    };
});

define('amd-named-modules/lib2', ['exports'], function (exports) {
    exports.exportedVar = 123; // def=moduleImport("amd-named-modules").getMember("exports").getMember("lib2").getMember("exportedVar")
});

define('amd-named-modules', ['amd-named-modules/lib', 'amd-named-modules/lib2'], function(foo, lib2) {
    return {
        bar: foo.foo, // def=moduleImport("amd-named-modules").getMember("exports").getMember("bar")
        lib2,
    }
});
