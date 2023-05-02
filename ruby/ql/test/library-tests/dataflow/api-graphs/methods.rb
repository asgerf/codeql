class MethodDefs < MethodDefsBase #$ use=getMember("MethodDefsBase")
    def foo(x, y)
        x.bar #$ use=getMember("MethodDefsBase").getASubclass().getInstance().getMethod("foo").getParameter(0).getMethod("bar").getReturn()
        123 #$ def=getMember("MethodDefsBase").getASubclass().getInstance().getMethod("foo").getReturn()
    end
end
