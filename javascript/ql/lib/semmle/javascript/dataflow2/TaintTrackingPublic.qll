private import javascript

/**
 * Holds if taint propagates from `source` to `sink` in zero or more local
 * (intra-procedural) steps.
 */
pragma[inline]
predicate localTaint(DataFlow::Node source, DataFlow::Node sink) { localTaintStep*(source, sink) }

/**
 * Holds if taint propagates from `nodeFrom` to `nodeTo` in exactly one local
 * (intra-procedural) step.
 */
predicate localTaintStep(DataFlow::Node source, DataFlow::Node sink) {
  // We don't currently use this in JS, but we provide it for consistency with other languages.
  TaintTracking::sharedTaintStep(source, sink)
  or
  source.getASuccessor() = sink
}
