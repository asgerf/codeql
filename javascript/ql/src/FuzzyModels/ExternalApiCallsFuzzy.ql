import javascript
private import semmle.javascript.FuzzyModels

query predicate ambiguousCalls(DataFlow::InvokeNode invoke, string packages) {
  packages = strictconcat(string p | invoke = getANodeFromPackage(p).getAnInvocation() | p, ", ") and
  exists(packages.indexOf(","))
}

query predicate externalCalls = externalCall/2;

from string package, string methodName, int numCalls
where numCalls = strictcount(externalCall(package, methodName))
select package, methodName, numCalls order by numCalls desc
