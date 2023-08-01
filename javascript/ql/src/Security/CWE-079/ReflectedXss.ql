/**
 * @name Reflected cross-site scripting
 * @description Writing user input directly to an HTTP response allows for
 *              a cross-site scripting vulnerability.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 6.1
 * @precision high
 * @id js/reflected-xss
 * @tags security
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 */

import javascript
import semmle.javascript.security.dataflow.ReflectedXssQuery
import Configuration::PathGraph

from Configuration::PathNode source, Configuration::PathNode sink
where Configuration::flowPath(source, sink)
select sink.getNode(), source, sink, "Cross-site scripting vulnerability due to a $@.",
  source.getNode(), "user-provided value"
