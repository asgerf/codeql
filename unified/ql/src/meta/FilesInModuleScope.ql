/**
 * @name Files in module scope
 * @description Files that are part of a module scope
 * @kind problem
 * @problem.severity recommendation
 * @id unified/meta/files-in-module-scope
 * @tags meta
 * @precision very-low
 */

private import unified
private import codeql.unified.internal.NameBindingPlugin

string getModuleName(ModuleScopeRepr scope) {
  result = strictconcat(string n | scope.hasImportableName(n) | n, ",")
  or
  not scope.hasImportableName(_) and
  result = scope.getFile().getRelativePath() + ":" + scope.getLocation().getStartColumn()
}

from File file, ModuleScopeRepr scope
where scope.getAnIncludedFile() = file
select file, "Included in $@", scope, getModuleName(scope)
