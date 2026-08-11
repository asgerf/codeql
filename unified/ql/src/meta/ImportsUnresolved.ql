/**
 * @name Unresolved imports
 * @description Imports whose target module could not be found
 * @kind problem
 * @problem.severity recommendation
 * @id unified/meta/unresolved-imports
 * @tags meta
 * @precision very-low
 */

private import unified
private import ImportUtil

from ImportDeclaration imprt
where not exists(getImportedModule(imprt))
select imprt, "Unresolved import"
