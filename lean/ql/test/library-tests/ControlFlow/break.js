function t1() {
    source("t1.1");
    while (foo()) {
        source("t1.2");
        break;
        sink(); // $ MISSING: unreachable SPURIOUS: dominatedBy=t1.1 dominatedBy=t1.2
    }
}
