// generated by codegen, do not edit
import codeql.rust.elements
import TestUtils

from MacroStmts x, string hasExpr, int getNumberOfStatements
where
  toBeTested(x) and
  not x.isUnknown() and
  (if x.hasExpr() then hasExpr = "yes" else hasExpr = "no") and
  getNumberOfStatements = x.getNumberOfStatements()
select x, "hasExpr:", hasExpr, "getNumberOfStatements:", getNumberOfStatements
