const foo = require("foo");

while(foo)
  foo = foo.foo; /* use=moduleImport("foo").getMember("foo") */ /* use=moduleImport("foo").getMember("foo").getMember("foo") */
