import * as t from '@example/flow-summary';

function m1() {
  sink(t.flowThrough(source())); // NOT OK
  sink(t.flowThrough(source() + "x")); // NOT OK
  sink(t.flowThrough("x")); // OK
}

function m2() {
  sink(t.flowIntoProp(source()).prop); // NOT OK
  sink(t.flowIntoProp(source()).prop2); // OK
  sink(t.flowIntoProp(source())); // OK
}

function m3() {
  sink(t.flowOutOfProp({ prop: source() })); // NOT OK
  sink(t.flowOutOfProp({ prop2: source() })); // OK
  sink(t.flowOutOfProp(source())); // OK

  const obj = {};
  obj.prop = source();
  sink(t.flowOutOfProp(obj)); // NOT OK
  sink(obj); // OK
  sink(obj.prop); // NOT OK
}

function m4() {
  sink(t.flowIntoArrayElement(source()).pop()); // NOT OK
  sink(t.flowIntoArrayElement(source())[0]); // NOT OK [INCONSISTENCY]
  sink(t.flowIntoArrayElement(source())[Math.random()]); // NOT OK [INCONSISTENCY]
  sink(t.flowIntoArrayElement(source()).prop); // OK
}

function m5() {
  sink(t.flowThroughTaint(source())); // NOT OK
  sink(t.flowThroughTaint(source() + "x")); // NOT OK
  sink(t.flowThroughTaint("x")); // OK
}

async function m6() {
  sink(await t.flowIntoPromise(source())); // NOT OK
  t.flowIntoPromise(source()).then(value => sink(value)); // NOT OK
}

function m7() {
  sink(t.flowOutOfPromise(Promise.resolve(source()))); // NOT OK
  sink(t.flowOutOfPromise(Promise.resolve("safe").then(x => source()))); // NOT OK
  sink(t.flowOutOfPromise(Promise.resolve("safe").then(x => "safe"))); // OK
  sink(t.flowOutOfPromise(Promise.resolve(source()).then(x => "safe"))); // OK

  async function makePromise() {
    return source();
  }
  sink(t.flowOutOfPromise(makePromise())); // NOT OK
}

function m8() {
  sink(t.flowOutOfCallback(() => source())); // NOT OK
  sink(t.flowOutOfCallback((source))); // OK
}

function m9() {
  sink(t.flowIntoCallback(source(), x => sink(x))); // NOT OK
  sink(t.flowIntoCallback("safe", x => sink(x))); // OK
  sink(t.flowIntoCallback(source(), x => ignore(x))); // OK
  sink(t.flowIntoCallback("safe", x => ignore(x))); // OK
}

function m9() {
  sink(t.flowThroughCallback(source(), x => x)); // NOT OK
  sink(t.flowThroughCallback(source(), x => "safe")); // OK
  sink(t.flowThroughCallback("safe", x => x)); // OK
  sink(t.flowThroughCallback("safe", x => "safe")); // OK
}
