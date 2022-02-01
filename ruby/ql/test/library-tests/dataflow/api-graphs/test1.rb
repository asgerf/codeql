MyModule #$ use=getMember("MyModule")
print MyModule.foo #$ use=getMember("MyModule").getMethod("foo").getReturn()
Kernel.print(e) #$ use=getMember("Kernel").getMethod("print").getReturn()
Object::Kernel #$ use=getMember("Kernel")
Object::Kernel.print(e)  #$ use=getMember("Kernel").getMethod("print").getReturn()
begin
    print MyModule.bar #$ use=getMember("MyModule").getMethod("bar").getReturn()
    raise AttributeError #$ use=getMember("AttributeError")
rescue AttributeError => e #$ use=getMember("AttributeError")
    Kernel.print(e)  #$ use=getMember("Kernel").getMethod("print").getReturn()
end
Unknown.new.run #$ use=getMember("Unknown").getMethod("new").getReturn().getMethod("run").getReturn()
Foo::Bar::Baz #$ use=getMember("Foo").getMember("Bar").getMember("Baz")

Const = [1, 2, 3] #$ use=getMember("Array").getMethod("[]").getReturn()
Const.each do |c| #$ use=getMember("Const").getMethod("each").getReturn()
    puts c #$ use=getMember("Const").getMethod("each").getBlock().getParameter(0)
end

foo = Foo #$ use=getMember("Foo")
foo::Bar::Baz #$ use=getMember("Foo").getMember("Bar").getMember("Baz")

FooAlias = Foo #$ use=getMember("Foo")
FooAlias::Bar::Baz #$ use=getMember("Foo").getMember("Bar").getMember("Baz")

module Outer
    module Inner
    end
end

Outer::Inner.foo #$ use=getMember("Outer").getMember("Inner").getMethod("foo").getReturn()
