import 'dummy';

function f() {
    let captured;
    function inner() { captured = "sdf"; return captured; }

    captured = [source(), "safe"];
    sink(captured); // NOT OK [INCONSISTENCY] - no implicit read of ArrayElement
    g.apply(undefined, captured);
}

function g(x, y) {
    sink(x); // NOT OK
    sink(y); // OK
}
