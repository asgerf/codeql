const testlib = require('testlib');
const util = require('util');
const EventEmitter = require('events');

function MyStream() {
    EventEmitter.call(this);
}

util.inherits(MyStream, EventEmitter);

MyStream.prototype.write = (data) => this.emit('data', data);

function MyOtherStream() { /* use=moduleImport("testlib").getParameter(0).getMember("MyOtherStream").getInstance() */
    EventEmitter.call(this);
}

util.inherits(MyOtherStream, EventEmitter);

MyOtherStream.prototype.write = function (data) { /* use=moduleImport("testlib").getParameter(0).getMember("MyOtherStream").getInstance() */
    this.emit('data', data);
    return this;
};

MyOtherStream.prototype.instanceProp = 1; /* def=moduleImport("testlib").getParameter(0).getMember("MyOtherStream").getInstance().getMember("instanceProp") */

MyOtherStream.classProp = 1; /* def=moduleImport("testlib").getParameter(0).getMember("MyOtherStream").getMember("classProp") */

testlib({ MyOtherStream });
