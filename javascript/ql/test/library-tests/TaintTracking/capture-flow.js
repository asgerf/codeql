import 'dummy';

function outerMost() {
    function outer() {
        var captured;
        function f(x) {
            captured = x;
        }
        f(source());

        return captured;
    }

    sink(outer()); // NOT OK

    return outer();
}

sink(outerMost()); // NOT OK

function confuse(x) {
    let captured;
    function f() {
        captured = x;
    }
    f();
    return captured;
}

sink(confuse('safe')); // OK
sink(confuse(source())); // NOT OK

function test3(param) {
    var x;
    function one() {
        x = param;
    }
    function two() {
        one();
        return x;
    }
    return two();
}

sink(test3(source())); // NOT OK
sink(test3("safe")); // OK

function test4() {
    var x = source();
    return () => x;
}
sink(test4()()); // NOT OK

function test5(x) {
    return () => x;
}
sink(test5(source())()); // NOT OK
