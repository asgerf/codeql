import javascript
private import semmle.javascript.FuzzyModels

query predicate ambiguousCalls(DataFlow::InvokeNode invoke, string packages) {
  packages = strictconcat(string p | invoke = getANodeFromPackage(p).getAnInvocation() | p, ", ") and
  exists(packages.indexOf(","))
}

query DataFlow::InvokeNode externalCall(string package, string methodName) {
  result = getANamedExternalCall(package, methodName)
  or
  methodName = "(direct call)" and
  result = getADirectExternalCall(package)
  or
  methodName = "(anonymous call)" and
  result = getAnAnonymousExternalCall(package)
}

from string package, string methodName, int numCalls
where numCalls = strictcount(externalCall(package, methodName))
select package, methodName, numCalls order by numCalls desc
