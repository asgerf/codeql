// generated by codegen, do not edit
import codeql.rust.elements
import TestUtils

from
  FnPtrType x, string hasAbi, string isAsync, string isConst, string isUnsafe, string hasParamList,
  string hasRetType
where
  toBeTested(x) and
  not x.isUnknown() and
  (if x.hasAbi() then hasAbi = "yes" else hasAbi = "no") and
  (if x.isAsync() then isAsync = "yes" else isAsync = "no") and
  (if x.isConst() then isConst = "yes" else isConst = "no") and
  (if x.isUnsafe() then isUnsafe = "yes" else isUnsafe = "no") and
  (if x.hasParamList() then hasParamList = "yes" else hasParamList = "no") and
  if x.hasRetType() then hasRetType = "yes" else hasRetType = "no"
select x, "hasAbi:", hasAbi, "isAsync:", isAsync, "isConst:", isConst, "isUnsafe:", isUnsafe,
  "hasParamList:", hasParamList, "hasRetType:", hasRetType
