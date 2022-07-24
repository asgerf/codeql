anotherUnknownFunction().foo = 42; /* MISSING: def=moduleExport("imprecise-export").getMember("foo") */

module.exports = unknownFunction();
