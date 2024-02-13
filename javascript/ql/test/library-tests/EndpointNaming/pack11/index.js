function wrap(fn) {
    // This closure is exposed as both 'foo' and 'bar' (with different enclosing call contexts),
    // but we don't want to see 'foo' and 'bar' as aliases
    return x => fn(x);
}

function foo1(x) {} // $ method=(pack11).foo
export const foo = wrap(foo1);

function bar1(x) {} // $ method=(pack11).bar
export const bar = wrap(bar1);

export function baz(x) {
    return foo(x);
} // $ method=(pack11).baz
