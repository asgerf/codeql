// generated by codegen
import codeql.rust.elements
import TestUtils

from BreakExpr x, string hasExpr, string hasLabel
where
  toBeTested(x) and
  not x.isUnknown() and
  (if x.hasExpr() then hasExpr = "yes" else hasExpr = "no") and
  if x.hasLabel() then hasLabel = "yes" else hasLabel = "no"
select x, "hasExpr:", hasExpr, "hasLabel:", hasLabel
