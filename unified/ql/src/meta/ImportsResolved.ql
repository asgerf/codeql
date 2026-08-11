/**
 * @name Resolved imports
 * @description Imports whose target module was found
 * @kind problem
 * @problem.severity recommendation
 * @id unified/meta/resolved-imports
 * @tags meta
 * @precision very-low
 */

private import unified
private import ImportUtil

from ImportDeclaration imprt
where exists(getImportedModule(imprt))
select imprt, "Resolved import"
