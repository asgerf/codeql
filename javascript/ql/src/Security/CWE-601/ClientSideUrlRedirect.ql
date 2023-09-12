/**
 * @name Client-side URL redirect
 * @description Client-side URL redirection based on unvalidated user input
 *              may cause redirection to malicious web sites.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 6.1
 * @precision high
 * @id js/client-side-unvalidated-url-redirection
 * @tags security
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 *       external/cwe/cwe-601
 */

import javascript
import semmle.javascript.security.dataflow.ClientSideUrlRedirectQuery
import ClientSideUrlRedirectFlow::PathGraph

from ClientSideUrlRedirectFlow::PathNode source, ClientSideUrlRedirectFlow::PathNode sink
where ClientSideUrlRedirectFlow::flowPath(source, sink)
select sink.getNode(), source, sink, "Untrusted URL redirection depends on a $@.", source.getNode(),
  "user-provided value"
