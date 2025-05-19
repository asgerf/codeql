function t1() {
    source("t1");
    sink(); // $ dominatedBy=t1
}

function t2(x) {
    source("t2.1");
    if (x) {
        source("t2.2");
        sink(); // $ dominatedBy=t2.1 dominatedBy=t2.2
    } else {
        source("t2.3");
        sink(); // $ dominatedBy=t2.1 dominatedBy=t2.3
    }
    sink(); // $ dominatedBy=t2.1 reachedBy=t2.2 reachedBy=t2.3
}

function t3(x) {
    if (source("t3.1") && source("t3.2")) {
        sink() // $ dominatedBy=t3.1-true dominatedBy=t3.2-true
    } else {
        sink(); // $ dominatedBy=t3.1 reachedBy=t3.2-false
    }
}

function t4(x) {
    if (source("t4.1") || source("t4.2")) {
        sink() // $ dominatedBy=t4.1 reachedBy=t4.2-true
    } else {
        sink(); // $ dominatedBy=t4.1-false dominatedBy=t4.2-false
    }
}

function t5(x) {
    if (!(source("t5.1") && source("t5.2"))) {
        sink() // $ dominatedBy=t5.1 reachedBy=t5.2-false
    } else {
        sink(); // $ dominatedBy=t5.1-true dominatedBy=t5.2-true
    }
}

function t6(x) {
    if (!(source("t6.1") || source("t6.2"))) {
        sink() // $ dominatedBy=t6.1-false dominatedBy=t6.2-false
    } else {
        sink(); // $ dominatedBy=t6.1 reachedBy=t6.2-true
    }
}
