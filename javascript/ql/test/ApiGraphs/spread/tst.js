const lib = require('something');

function f() {
    return {
        x: new Object() /* def=moduleImport("something").getMember("m1").getParameter(0).getMember("x") */
    }
}

lib.m1({
    ...f()
})
