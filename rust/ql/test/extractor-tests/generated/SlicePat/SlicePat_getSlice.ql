// generated by codegen
import codeql.rust.elements
import TestUtils

from SlicePat x
where toBeTested(x) and not x.isUnknown()
select x, x.getSlice()
