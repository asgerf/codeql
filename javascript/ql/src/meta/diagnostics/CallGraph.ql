/**
 * @name Call graph
 * @description An edge in the call graph.
 * @kind problem
 * @problem.severity recommendation
 * @id js/diagnostics/call-graph
 * @tags diagnostics-internal
 * @precision very-low
 */

import javascript

from DataFlow::InvokeNode invoke, Function f
where invoke.getACallee() = f
select invoke, "Call to $@", f, f.describe()
