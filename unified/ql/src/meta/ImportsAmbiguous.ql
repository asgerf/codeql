/**
 * @name Ambiguous imports
 * @description Imports for which multiple target modules were found
 * @kind problem
 * @problem.severity recommendation
 * @id unified/meta/ambiguous-imports
 * @tags meta
 * @precision very-low
 */

private import unified
private import ImportUtil

from ImportDeclaration imprt
where strictcount(getImportedModule(imprt)) > 1
select imprt, "Unresolved import"
