/**
 * @name Missing rate limiting
 * @description An HTTP request handler that performs expensive operations without
 *              restricting the rate at which operations can be carried out is vulnerable
 *              to denial-of-service attacks.
 * @kind problem
 * @problem.severity error
 * @security-severity 7.5
 * @precision high
 * @id js/missing-rate-limiting
 * @tags security
 *       external/cwe/cwe-770
 *       external/cwe/cwe-307
 *       external/cwe/cwe-400
 */

import javascript
import semmle.javascript.security.dataflow.MissingRateLimiting
import semmle.javascript.RestrictedLocations

from
  ExpensiveRouteHandler r, string explanation, DataFlow::Node reference, string referenceLabel
where
  r.explain(explanation, reference, referenceLabel) and
  not r.isGuardedBy(any(RateLimitingMiddleware m))
select r.getAstNode().(FirstLineOf), "This route handler " + explanation + ", but is not rate-limited.",
  reference, referenceLabel
