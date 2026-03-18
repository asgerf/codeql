function t1() {
    const source = require('testlib').getSource() // $ Source=t1
    require('testlib').mySink(source); // $ Alert=t1
}
