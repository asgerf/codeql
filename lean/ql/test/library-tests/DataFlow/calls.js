function t1() {
    function f(x) {
        sink(x); // $ MISSING: hasValueFlow=t1.1
    }
    f(source("t1.1"));
}
