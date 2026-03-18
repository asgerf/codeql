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
