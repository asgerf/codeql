/**
 * Contains the language-specific part of the models-as-data implementation found in `Shared.qll`.
 *
 * It must export the following members:
 * - The `Unit` class
 * - The `API` module (API graphs)
 * - `isPackageUsed(string package)`
 * - `getExtraNodeFromPath(string package, string type, string path)`
 * - `getExtraApiGraphLabelFromPathToken(string token)`
 */

import javascript as js
private import Shared

class Unit = js::Unit;

module API = js::API;

private module DataFlow = js::DataFlow;

/**
 * Holds if models describing `package` may be relevant for the analysis of this database.
 */
predicate isPackageUsed(string package) {
  exists(DataFlow::moduleImport(package))
  or
  package = "global"
  or
  exists(API::Node::ofType(package, _))
}

/** Holds if `global` is a global variable referenced via a the `global` package in a CSV row. */
private predicate isRelevantGlobal(string global) {
  exists(string path |
    isRelevantFullPath("global", "", path) and
    getExtraApiGraphLabelFromPathToken(path.splitAt(".", 0)) = API::EdgeLabel::member(global)
  )
}

/** An API graph entry point for global variables mentioned in a model. */
private class GlobalApiEntryPoint extends API::EntryPoint {
  string global;

  GlobalApiEntryPoint() {
    isRelevantGlobal(global) and
    this = "GlobalApiEntryPoint:" + global
  }

  override DataFlow::SourceNode getAUse() { result = DataFlow::globalVarRef(global) }

  override DataFlow::Node getARhs() { none() }

  /** Gets the name of the global variable. */
  string getGlobal() { result = global }
}

/**
 * Gets an API node referring to the given global variable (if relevant).
 */
private API::Node getGlobalNode(string globalName) {
  result = API::root().getASuccessor(any(GlobalApiEntryPoint e | e.getGlobal() = globalName))
}

/** Gets a JavaScript-specific interpretation of the given `(package, type, path)` tuple. */
API::Node getExtraNodeFromPath(string package, string type, string path) {
  // Global variable accesses is via the 'global' package
  exists(string globalName |
    result = getGlobalNode(globalName) and
    package = getAPackageAlias("global") and
    type = "" and
    path = "Member[" + globalName + "]"
  )
  or
  // Access instance of a type based on type annotations
  path = "" and
  result = API::Node::ofType(getAPackageAlias(package), type)
}

/** Gets a JavaScript-specific API graph label corresponding to the given access path token */
bindingset[token]
string getExtraApiGraphLabelFromPathToken(string token) {
  token = "Instance" and
  result = API::EdgeLabel::instance()
  or
  token = "Awaited" and
  result = API::EdgeLabel::promised()
  or
  token = "ArrayElement" and
  result = API::EdgeLabel::member(DataFlow::PseudoProperties::arrayElement())
  or
  token = "Element" and
  result = API::EdgeLabel::member(DataFlow::PseudoProperties::arrayLikeElement())
  or
  // Note: MapKey not currently supported
  token = "MapValue" and
  result = API::EdgeLabel::member(DataFlow::PseudoProperties::mapValueAll())
}

/**
 * A remote flow source originating from a CSV source row.
 */
private class RemoteFlowSourceFromCsv extends js::RemoteFlowSource {
  RemoteFlowSourceFromCsv() { this = ModelOutput::getASourceNode("remote").getAnImmediateUse() }

  override string getSourceType() { result = "Remote flow" }
}

/**
 * Like `ModelOutput::summaryStep` but with API nodes mapped to data-flow nodes.
 */
private predicate summaryStepNodes(DataFlow::Node pred, DataFlow::Node succ, string kind) {
  exists(API::Node predNode, API::Node succNode |
    ModelOutput::summaryStep(predNode, succNode, kind) and
    pred = predNode.getARhs() and
    succ = succNode.getAnImmediateUse()
  )
}

/** Data flow steps induced by summary models of kind `value`. */
private class DataFlowStepFromSummary extends DataFlow::SharedFlowStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    summaryStepNodes(pred, succ, "value")
  }
}

/** Taint steps induced by summary models of kind `taint`. */
private class TaintStepFromSummary extends js::TaintTracking::SharedTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    summaryStepNodes(pred, succ, "taint")
  }
}
