function t1() {
    sink(source("t1.1")); // $ hasValueFlow=t1.1
    sink(source("t1.2")); // $ hasValueFlow=t1.2
}
