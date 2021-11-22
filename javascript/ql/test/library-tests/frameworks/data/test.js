import * as testlib from 'testlib';
import { preserveTaint } from 'testlib';

function testPreserveTaint(x) {
  sink(testlib.preserveTaint(source())); // NOT OK
  sink(preserveTaint(source())); // NOT OK
  sink(require('testlib').preserveTaint(source())); // NOT OK
  sink(require('testlib').preserveTaint('safe')); // OK
  sink(require('testlib').preserveTaint(1, source())); // OK
}

function testTaintIntoCallback(x) {
  testlib.taintIntoCallback(source(), y => {
    sink(y); // NOT OK
  });
  testlib.taintIntoCallback('safe', y => {
    sink(y); // OK
  });
  testlib.taintIntoCallback(source(), undefined, y => {
    sink(y); // NOT OK
  });
  testlib.taintIntoCallback(source(), undefined, undefined, y => {
    sink(y); // OK - only callback 1-2 receive taint
  });
}

function testPreserveArgZeroAndTwo() {
  sink(testlib.preserveArgZeroAndTwo(source(), 1, 1, 1)); // NOT OK
  sink(testlib.preserveArgZeroAndTwo(1, source(), 1, 1)); // OK
  sink(testlib.preserveArgZeroAndTwo(1, 1, source(), 1)); // NOT OK
  sink(testlib.preserveArgZeroAndTwo(1, 1, 1, source())); // OK
}

function testPreserveAllButFirstArgument() {
  sink(testlib.preserveAllButFirstArgument(source(), 1, 1, 1)); // OK
  sink(testlib.preserveAllButFirstArgument(1, source(), 1, 1)); // NOT OK
  sink(testlib.preserveAllButFirstArgument(1, 1, source(), 1)); // NOT OK
  sink(testlib.preserveAllButFirstArgument(1, 1, 1, source())); // NOT OK
}
