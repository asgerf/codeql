function t1() {
    const source = require('testlib').getSource() // $ Source=t1
    require('testlib').mySink(source); // $ Alert=t1
}

function t2() {
    const { sourceProp } = require('testlib').getSourceInProp(); // $ Source=t2
    require('testlib').mySinkInProp({ sinkProp: sourceProp }); // $ Alert=t2
}

function t3() {
    require('testlib').getSourceInCallback(x => { // $ Source=t3
        require('testlib').mySink(x); // $ Alert=t3
    });
}

function t4() {
    const wrapper = { lib: require('testlib') };
    const source = wrapper.lib.getSource() // $ Source=t4
    wrapper.lib.mySink(source); // $ Alert=t4
}

function t5() {
    function getLib() {
        return require('testlib');
    }
    function takeLib(lib) {
        const source = lib.getSource() // $ Source=t5.1
        lib.mySink(source); // $ Alert=t5.1
    }
    function takeWrapper(wrapper) {
        const source = wrapper.lib.getSource() // $ Source=t5.2
        wrapper.lib.mySink(source); // $ Alert=t5.2
    }
    takeLib(getLib());
    takeWrapper({lib: getLib()});
}

function t6() {
    require('testlib').something().complicated(x => {
        const source = x.fuzzySource; // $ Source=t6
        x.blah().fuzzySink(source); // $ Alert=t6
    })
}

function t7() {
    const source = require('testlib').getSource(); // $ Source=t7

    require('testlib').arity2Sink(source);
    require('testlib').arity2Sink(source, true); // $ Alert=t7
    require('testlib').arity2Sink(source, true, true); // $ MISSING: Alert=t7

    require('testlib').stringArgSink("safe", source);
    require('testlib').stringArgSink("unsafe", source); // $ Alert=t7

    require('testlib').lastArgSink(source); // $ Alert=t7

    require('testlib').lastArgSink(source, "x");
    require('testlib').lastArgSink("x", source); // $ Alert=t7

    require('testlib').lastArgSink(source, "x", "x");
    require('testlib').lastArgSink("x", source, "x");
    require('testlib').lastArgSink("x", "x", source); // $ Alert=t7
}
