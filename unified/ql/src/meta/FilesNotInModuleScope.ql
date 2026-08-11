/**
 * @name Files not in any module scope
 * @description Files that are not part of any module scope
 * @kind problem
 * @problem.severity recommendation
 * @id unified/meta/files-not-in-module-scope
 * @tags meta
 * @precision very-low
 */

private import unified
private import codeql.unified.internal.NameBindingPlugin

from File file
where
  not file = any(ModuleScopeRepr s).getAnIncludedFile() and
  file = any(TopLevel t).getFile()
select file, "Not included in any module scope"
