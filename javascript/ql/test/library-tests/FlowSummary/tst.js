import * as t from '@example/flow-summary';

function m1() {
  sink(t.flowThrough(source())); // NOT OK
  sink(t.flowThrough(source() + "x")); // OK - we are not tracking taint in this test
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
  sink(t.flowOutOfInnerCallback(cb => { cb(source()); })); // NOT OK [INCONSISTENCY]
}

async function m6() {
  sink(t.flowOutOfPromise(t.flowIntoPromise(source()))); // NOT OK (although the synchronous flow is technically not possible)

  let data = { prop: source() };
  sink(t.flowOutOfPromise(t.flowIntoPromise(data)).prop); // NOT OK
  sink(t.flowOutOfPromise(t.flowIntoPromise(t.flowIntoPromise(data))).prop); // NOT OK
  sink(t.flowOutOfPromise(t.flowOutOfPromise(t.flowIntoPromise(data))).prop); // NOT OK
  sink(t.flowOutOfPromise(data).prop); // NOT OK - because Awaited allows pass-through of a non-promise value
  sink(t.flowIntoPromise(data).prop); // OK - promise object does not have the 'prop' property
}

async function m7() {
  sink(t.flowOutOfPromise(Promise.resolve(source()))); // NOT OK
  sink(t.flowOutOfPromise(Promise.resolve("safe").then(x => source()))); // NOT OK
  sink(t.flowOutOfPromise(Promise.resolve("safe").then(x => "safe"))); // OK
  sink(t.flowOutOfPromise(Promise.resolve(source()).then(x => "safe"))); // OK

  sink(t.flowOutOfPromise(Promise.reject(source()))); // OK
  sink(t.flowOutOfPromise(Promise.reject(source()).then(x => "safe", y => y))); // NOT OK
  sink(t.flowOutOfPromise(Promise.reject(source()).then(x => x, y => "safe"))); // OK
  sink(t.flowOutOfPromise(Promise.reject("safe").then(x => x, y => y))); // OK

  sink(t.flowOutOfPromise(Promise.reject(source()))); // OK
  sink(t.flowOutOfPromise(Promise.reject(source()).catch(err => err))); // NOT OK
  sink(t.flowOutOfPromise(Promise.reject(source()).catch(err => "safe"))); // OK
  sink(t.flowOutOfPromise(Promise.reject("safe").catch(err => err))); // OK

  sink(t.flowOutOfPromise(Promise.reject(source()).then(x => "safe").catch(err => err))); // NOT OK

  sink(t.flowOutOfPromise(Promise.reject(source()).finally(() => "safe").catch(err => err))); // NOT OK
  sink(t.flowOutOfPromise(Promise.resolve(source()).finally(() => "safe").then(err => err))); // NOT OK
  sink(t.flowOutOfPromise(Promise.reject("safe").finally(() => { throw source() }).catch(err => err))); // NOT OK

  Promise.resolve("safe")
    .then(x => { throw source(); })
    .catch(err => {
      sink(err); // NOT OK
    });

  Promise.resolve("safe")
    .then(x => { throw source(); })
    .then(x => "safe")
    .catch(err => {
      sink(err); // NOT OK
    });

  sink(await t.flowIntoPromise(source())); // NOT OK [INCONSISTENCY]
  t.flowIntoPromise(source()).then(value => sink(value)); // NOT OK
  sink(await t.flowIntoPromise(t.flowIntoPromise(source()))); // NOT OK [INCONSISTENCY]

  async function makePromise() {
    return source();
  }
  sink(t.flowOutOfPromise(makePromise())); // NOT OK [INCONSISTENCY]

  let taintedPromise = new Promise((resolve, reject) => resolve(source()));
  sink(t.flowOutOfPromise(taintedPromise)); // NOT OK

  new Promise((resolve, reject) => resolve(source())).then(x => sink(x)); // NOT OK
  new Promise((resolve, reject) => resolve(source())).catch(err => sink(err)); // OK
  new Promise((resolve, reject) => reject(source())).then(x => sink(x)); // OK
  new Promise((resolve, reject) => reject(source())).catch(err => sink(err)); // NOT OK
}

function m8() {
  sink(t.flowOutOfCallback(() => source())); // NOT OK
  sink(t.flowOutOfCallback((source))); // OK

  function sourceCallback() {
    return source();
  }
  sink(t.flowOutOfCallback(sourceCallback)); // NOT OK
}

function m9() {
  sink(t.flowIntoCallback(source(), x => sink(x))); // NOT OK
  sink(t.flowIntoCallback("safe", x => sink(x))); // OK
  sink(t.flowIntoCallback(source(), x => ignore(x))); // OK
  sink(t.flowIntoCallback("safe", x => ignore(x))); // OK
}

function m10() {
  sink(t.flowThroughCallback(source(), x => x)); // NOT OK
  sink(t.flowThroughCallback(source(), x => "safe")); // OK
  sink(t.flowThroughCallback("safe", x => x)); // OK
  sink(t.flowThroughCallback("safe", x => "safe")); // OK
}

function m11() {
  let data = t.flowFromSideEffectOnParameter(param => {
    param.prop = source();
  });
  sink(data); // NOT OK

  function manullyWritten(param) {
    param.prop = source();
  }
  let obj = {};
  manullyWritten(obj);
  sink(obj.prop); // NOT OK
}

function m12() {
  Promise.all([
    t.flowIntoPromise(source()),
    source(),
    "safe"
  ]).then(([x1, x2, x3]) => {
    sink(x1); // NOT OK
    sink(x2); // NOT OK
    sink(x3); // OK
  });
}
