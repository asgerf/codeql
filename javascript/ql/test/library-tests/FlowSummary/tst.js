function m1() {
  const flowThrough = mkSummary("Argument[0]", "ReturnValue");
  sink(flowThrough(source())); // NOT OK
  sink(flowThrough(source() + "x")); // OK - we are not tracking taint in this test
  sink(flowThrough("x")); // OK
}

function m2() {
  const flowIntoProp = mkSummary("Argument[0]", "ReturnValue.Member[prop]");
  sink(flowIntoProp(source()).prop); // NOT OK
  sink(flowIntoProp(source()).prop2); // OK
  sink(flowIntoProp(source())); // OK
}

function m3() {
  const flowOutOfProp = mkSummary("Argument[0].Member[prop]", "ReturnValue");
  sink(flowOutOfProp({ prop: source() })); // NOT OK
  sink(flowOutOfProp({ prop2: source() })); // OK
  sink(flowOutOfProp(source())); // OK

  const obj = {};
  obj.prop = source();
  sink(flowOutOfProp(obj)); // NOT OK
  sink(obj); // OK
  sink(obj.prop); // NOT OK
}

function m4() {
  const flowIntoArrayElement = mkSummary("Argument[0]", "ReturnValue.ArrayElement");
  sink(flowIntoArrayElement(source()).pop()); // NOT OK
  sink(flowIntoArrayElement(source())[0]); // NOT OK [INCONSISTENCY]
  sink(flowIntoArrayElement(source())[Math.random()]); // NOT OK [INCONSISTENCY]
  sink(flowIntoArrayElement(source()).prop); // OK
}

function m5() {
  const flowOutOfInnerCallback = mkSummary("Argument[0].Parameter[0].Argument[0]", "ReturnValue");
  sink(flowOutOfInnerCallback(cb => { cb(source()); })); // NOT OK [INCONSISTENCY]
}

async function m6() {
  const flowOutOfPromise = mkSummary("Argument[0].Awaited", "ReturnValue");
  const flowIntoPromise = mkSummary("Argument[0]", "ReturnValue.Awaited");

  sink(flowOutOfPromise(flowIntoPromise(source()))); // NOT OK (although the synchronous flow is technically not possible)

  let data = { prop: source() };
  sink(flowOutOfPromise(flowIntoPromise(data)).prop); // NOT OK
  sink(flowOutOfPromise(flowIntoPromise(flowIntoPromise(data))).prop); // NOT OK
  sink(flowOutOfPromise(flowOutOfPromise(flowIntoPromise(data))).prop); // NOT OK
  sink(flowOutOfPromise(data).prop); // NOT OK - because Awaited allows pass-through of a non-promise value
  sink(flowIntoPromise(data).prop); // OK - promise object does not have the 'prop' property

  sink(flowOutOfPromise(Promise.resolve(source()))); // NOT OK
  sink(flowOutOfPromise(Promise.resolve("safe").then(x => source()))); // NOT OK
  sink(flowOutOfPromise(Promise.resolve("safe").then(x => "safe"))); // OK
  sink(flowOutOfPromise(Promise.resolve(source()).then(x => "safe"))); // OK

  sink(flowOutOfPromise(Promise.reject(source()))); // OK
  sink(flowOutOfPromise(Promise.reject(source()).then(x => "safe", y => y))); // NOT OK
  sink(flowOutOfPromise(Promise.reject(source()).then(x => x, y => "safe"))); // OK
  sink(flowOutOfPromise(Promise.reject("safe").then(x => x, y => y))); // OK

  sink(flowOutOfPromise(Promise.reject(source()))); // OK
  sink(flowOutOfPromise(Promise.reject(source()).catch(err => err))); // NOT OK
  sink(flowOutOfPromise(Promise.reject(source()).catch(err => "safe"))); // OK
  sink(flowOutOfPromise(Promise.reject("safe").catch(err => err))); // OK

  sink(flowOutOfPromise(Promise.reject(source()).then(x => "safe").catch(err => err))); // NOT OK

  sink(flowOutOfPromise(Promise.reject(source()).finally(() => "safe").catch(err => err))); // NOT OK
  sink(flowOutOfPromise(Promise.resolve(source()).finally(() => "safe").then(err => err))); // NOT OK
  sink(flowOutOfPromise(Promise.reject("safe").finally(() => { throw source() }).catch(err => err))); // NOT OK

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

  sink(await flowIntoPromise(source())); // NOT OK
  flowIntoPromise(source()).then(value => sink(value)); // NOT OK
  sink(await flowIntoPromise(flowIntoPromise(source()))); // NOT OK

  async function makePromise() {
    return source();
  }
  sink(flowOutOfPromise(makePromise())); // NOT OK

  let taintedPromise = new Promise((resolve, reject) => resolve(source()));
  sink(flowOutOfPromise(taintedPromise)); // NOT OK

  new Promise((resolve, reject) => resolve(source())).then(x => sink(x)); // NOT OK
  new Promise((resolve, reject) => resolve(source())).catch(err => sink(err)); // OK
  new Promise((resolve, reject) => reject(source())).then(x => sink(x)); // OK
  new Promise((resolve, reject) => reject(source())).catch(err => sink(err)); // NOT OK

  Promise.all([
    flowIntoPromise(source()),
    source(),
    "safe"
  ]).then(([x1, x2, x3]) => {
    sink(x1); // NOT OK
    sink(x2); // NOT OK
    sink(x3); // OK
  });
}

function m8() {
  const flowOutOfCallback = mkSummary("Argument[0].ReturnValue", "ReturnValue");

  sink(flowOutOfCallback(() => source())); // NOT OK
  sink(flowOutOfCallback((source))); // OK

  function sourceCallback() {
    return source();
  }
  sink(flowOutOfCallback(sourceCallback)); // NOT OK
}

function m9() {
  const flowIntoCallback = mkSummary("Argument[0]", "Argument[1].Parameter[0]");

  sink(flowIntoCallback(source(), x => sink(x))); // NOT OK
  sink(flowIntoCallback("safe", x => sink(x))); // OK
  sink(flowIntoCallback(source(), x => ignore(x))); // OK
  sink(flowIntoCallback("safe", x => ignore(x))); // OK
}

function m10() {
  const flowThroughCallback = mkSummary([
    ["Argument[0]", "Argument[1].Parameter[0]"],
    ["Argument[1].ReturnValue", "ReturnValue"]
  ]);

  sink(flowThroughCallback(source(), x => x)); // NOT OK
  sink(flowThroughCallback(source(), x => "safe")); // OK
  sink(flowThroughCallback("safe", x => x)); // OK
  sink(flowThroughCallback("safe", x => "safe")); // OK
}

function m11() {
  const flowFromSideEffectOnParameter = mkSummary("Argument[0].Parameter[0].Member[prop]", "ReturnValue");

  let data = flowFromSideEffectOnParameter(param => {
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

async function m13() {
  async function testStoreBack(x) {
    (await x).prop = source();
  }
  const obj = {};
  const promise = Promise.resolve(obj);
  testStoreBack(promise);
  sink(obj.prop); // NOT OK [INCONSISTENCY]
  sink(promise.prop); // OK [INCONSISTENCY]
  sink((await promise).prop); // NOT OK

  const obj2 = {};
  testStoreBack(obj2);
  sink(obj2.prop);; // NOT OK
}
