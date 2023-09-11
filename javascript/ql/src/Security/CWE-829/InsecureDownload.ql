/**
 * @name Download of sensitive file through insecure connection
 * @description Downloading executables and other sensitive files over an insecure connection
 *              opens up for potential man-in-the-middle attacks.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 8.1
 * @precision high
 * @id js/insecure-download
 * @tags security
 *       external/cwe/cwe-829
 */

import javascript
import semmle.javascript.security.dataflow.InsecureDownloadQuery
import InsecureDownload::PathGraph

from InsecureDownload::PathNode source, InsecureDownload::PathNode sink
where InsecureDownload::flowPath(source, sink)
select sink.getNode(), source, sink, "$@ of sensitive file from $@.",
  sink.getNode().(Sink).getDownloadCall(), "Download", source.getNode(), "HTTP source"
