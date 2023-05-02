class MethodDefs < MethodDefsBase #$ use=getMember("MethodDefsBase")
    def foo(x, y)
        x.bar #$ use=getMember("MethodDefsBase").getASubclass().getInstance().getMethod("foo").getParameter(0).getMethod("bar").getReturn()
    end
end
