/**
 * @name Database query built from user-controlled sources
 * @description Building a database query from user-controlled sources is vulnerable to insertion of
 *              malicious code by the user.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 8.8
 * @precision high
 * @id js/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 *       external/cwe/cwe-090
 *       external/cwe/cwe-943
 */

import javascript
import semmle.javascript.dataflow2.DataFlow as DataFlow2
import semmle.javascript.security.dataflow.SqlInjectionQuery as SqlInjection
import semmle.javascript.security.dataflow.NosqlInjectionQuery as NosqlInjection

module Merged =
  DataFlow2::MergePathGraph<SqlInjection::Configuration::PathNode,
    NosqlInjection::Configuration::PathNode, SqlInjection::Configuration::PathGraph,
    NosqlInjection::Configuration::PathGraph>;

import Merged

from PathNode source, PathNode sink, string type
where
  SqlInjection::Configuration::flowPath(source.asPathNode1(), sink.asPathNode1()) and
  type = "string"
  or
  NosqlInjection::Configuration::flowPath(source.asPathNode2(), sink.asPathNode2()) and
  type = "object"
select sink.getNode(), source, sink, "This query " + type + " depends on a $@.", source.getNode(),
  "user-provided value"
