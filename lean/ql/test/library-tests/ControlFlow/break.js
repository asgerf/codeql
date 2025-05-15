function t1() {
    source("t1.1");
    while (foo()) {
        source("t1.2");
        break;
        sink(); // not reachable
    }
}
