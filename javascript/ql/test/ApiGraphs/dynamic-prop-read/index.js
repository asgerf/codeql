const MyStream = require('classes').MyStream;

var s = new MyStream();
for (let m of ["write"])
    s[m]("Hello, world!"); /* use=moduleImport("classes").getMember("MyStream").getInstance().getUnknownMember() */
