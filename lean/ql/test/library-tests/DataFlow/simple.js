function t1() {
    sink(source("t1.1")); // $ hasValueFlow=t1.1
    sink(source("t1.2")); // $ hasValueFlow=t1.2
}

function t2() {
    const x = source("t2.1");
    sink(x); // $ hasValueFlow=t2.1
    sink(x); // $ hasValueFlow=t2.1
    sink(y);
}

function t3() {
    const array = [source("t3.1"), source("t3.2")];
    sink(array[0]); // $ hasValueFlow=t3.1
    sink(array[1]); // $ hasValueFlow=t3.2
    for (let item of array) {
        sink(item); // $ hasValueFlow=t3.1 hasValueFlow=t3.2
    }
    sink(item); // nothing flows here
}
