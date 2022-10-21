class ResolvableBaseClass
end

class UnresolvedNamespace::Subclass1 < ResolvableBaseClass
end

class UnresolvedNamespace::Subclass2 < UnresolvedNamespace::Subclass1
end

module Foo
    class UnresolvedInsideFoo::Class1
    end
    class UnresolvedInsideFoo::Class2 < UnresolvedInsideFoo::Class1
    end
end
