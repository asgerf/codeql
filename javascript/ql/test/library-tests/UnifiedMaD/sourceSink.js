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
