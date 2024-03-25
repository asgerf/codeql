/**
 * Contains the language-specific part of the models-as-data implementation found in `ApiGraphModels.qll`.
 *
 * It must export the following members:
 * ```ql
 * class Unit // a unit type
 * class InvokeNode // a type representing an invocation connected to the API graph
 * module API // the API graph module
 * predicate isPackageUsed(string package)
 * API::Node getExtraNodeFromPath(string package, string type, string path, int n)
 * API::Node getExtraSuccessorFromNode(API::Node node, AccessPathTokenBase token)
 * API::Node getExtraSuccessorFromInvoke(InvokeNode node, AccessPathTokenBase token)
 * predicate invocationMatchesExtraCallSiteFilter(InvokeNode invoke, AccessPathTokenBase token)
 * InvokeNode getAnInvocationOf(API::Node node)
 * predicate isExtraValidTokenNameInIdentifyingAccessPath(string name)
 * predicate isExtraValidNoArgumentTokenInIdentifyingAccessPath(string name)
 * predicate isExtraValidTokenArgumentInIdentifyingAccessPath(string name, string argument)
 * ```
 */

private import javascript as JS
private import ApiGraphModels
private import codeql.dataflow.internal.AccessPathSyntax

// Re-export libraries needed by ApiGraphModels.qll
module API = JS::API;

import JS::DataFlow as DataFlow

/**
 * Holds if `rawType` represents the JavaScript type `qualifiedName` from the given NPM `package`.
 *
 * Type names have form `package.type` or just `package` if referring to the package export
 * object. If `package` contains a `.` character it must be enclosed in single quotes, such as `'package'.type`.
 */
bindingset[rawType]
predicate parseTypeString(string rawType, string package, string qualifiedName) {
  exists(string regexp |
    regexp = "('[^']+'|[^.]+)(.*)" and
    package = rawType.regexpCapture(regexp, 1).regexpReplaceAll("^'|'$", "") and
    qualifiedName = rawType.regexpCapture(regexp, 2).regexpReplaceAll("^\\.", "")
  )
}

/**
 * Holds if `rawType` is of form `(package).accessPath`.
 */
bindingset[rawType]
predicate parseValueAccessPath(string rawType, string package, string accessPath) {
  exists(string regexp |
    regexp = "\\(([^)]+)\\)(.*)" and
    package = rawType.regexpCapture(regexp, 1) and
    accessPath = rawType.regexpCapture(regexp, 2).regexpReplaceAll("^\\.", "")
  )
}

/**
 * Holds if models describing `package` may be relevant for the analysis of this database.
 */
predicate isPackageUsed(string package) {
  exists(DataFlow::moduleImport(package))
  or
  exists(JS::PackageJson json | json.getPackageName() = package)
  or
  package = "global"
  or
  any(DataFlow::SourceNode sn).hasUnderlyingType(package, _)
}

bindingset[type]
predicate isTypeUsed(string type) {
  exists(string package |
    (parseTypeString(type, package, _) or parseValueAccessPath(type, package, _)) and
    isPackageUsed(package)
  )
}

/**
 * Holds if `type` can be obtained from an instance of `otherType` due to
 * language semantics modeled by `getExtraNodeFromType`.
 */
predicate hasImplicitTypeModel(string type, string otherType) { none() }

pragma[nomagic]
private predicate parseRelevantTypeString(string rawType, string package, string qualifiedName) {
  isRelevantFullPath(rawType, _) and
  parseTypeString(rawType, package, qualifiedName)
}

/**
 * A string of form `(package).accessPath` appearing in a relevant `type` column.
 *
 * The `accessPath` is a dot-separated list of property names to be evaluated relative to the
 * package's root export object.
 *
 * Value-access paths are thus interpreted as values and property names. This is in contrast to
 * a type string of form `package.type` which refers to the TypeScript type `type` exported from `package`.
 * These paths are favored when generating a model from source code, as opposed to generating the
 * model from `.d.ts` files.
 *
 * In common cases `foo.C` will refer to instances of the class `C` from `foo`, whereas `(foo).C` will refer
 * to the class `C` itself. However, in general there is no way to know the relationship between values and types
 * without having access to the `.d.ts` file. We therefore support both formats when consuming models, and the
 * model generator is free to use either (or both) formats, depending on what the model is built from.
 */
private class ValueAccessPathString extends string {
  private string package;
  private string accessPath;

  ValueAccessPathString() {
    isRelevantFullPath(this, _) and
    parseValueAccessPath(this, package, accessPath)
  }

  string getPackageName() { result = package }

  string getAccessPath() { result = accessPath }

  pragma[nomagic]
  string getAccessPathComponent(int n) {
    result = accessPath.splitAt(".", n) and not accessPath = ""
  }

  pragma[nomagic]
  int getNumAccessPathComponent() { result = count(int n | exists(this.getAccessPathComponent(n))) }
}

/** Holds if `global` is a global variable referenced via a the `global` package in a CSV row. */
private predicate isRelevantGlobal(string global) {
  exists(AccessPath path, AccessPathToken token |
    isRelevantFullPath(["global", "(global)"], path) and
    token = path.getToken(0) and
    token.getName() = "Member" and
    global = token.getAnArgument()
  )
  or
  exists(ValueAccessPathString ap |
    ap.getPackageName() = "global" and
    global = ap.getAccessPathComponent(0)
  )
}

/** An API graph entry point for global variables mentioned in a model. */
private class GlobalApiEntryPoint extends API::EntryPoint {
  string global;

  GlobalApiEntryPoint() {
    isRelevantGlobal(global) and
    this = "GlobalApiEntryPoint:" + global
  }

  override DataFlow::SourceNode getASource() { result = DataFlow::globalVarRef(global) }

  /** Gets the name of the global variable. */
  string getGlobal() { result = global }
}

/**
 * Gets an API node referring to the given global variable (if relevant).
 */
private API::Node getGlobalNode(string globalName) {
  result = any(GlobalApiEntryPoint e | e.getGlobal() = globalName).getANode()
}

/** Gets a JavaScript-specific interpretation of the `(type, path)` tuple after resolving the first `n` access path tokens. */
bindingset[type, path]
API::Node getExtraNodeFromPath(string type, AccessPath path, int n) {
  // Global variable accesses is via the 'global' package
  exists(AccessPathToken token |
    type = ["global", "(global)"] and
    token = path.getToken(0) and
    token.getName() = "Member" and
    result = getGlobalNode(token.getAnArgument()) and
    n = 1
  )
}

private API::Node packageNode(string packageName) {
  result = API::Internal::getAModuleImportRaw(packageName)
  or
  result = API::moduleExport(packageName)
}

private API::Node getNodeFromValueAccessPath(ValueAccessPathString ap, int n) {
  n = 0 and
  result = packageNode(ap.getPackageName())
  or
  ap.getPackageName() = "global" and
  n = 1 and
  result = getGlobalNode(ap.getAccessPathComponent(0))
  or
  result = getNodeFromValueAccessPath(ap, n - 1).getMember(ap.getAccessPathComponent(n - 1))
}

private API::Node getNodeFromValueAccessPath(ValueAccessPathString ap) {
  result = getNodeFromValueAccessPath(ap, ap.getNumAccessPathComponent())
}

/** Gets a JavaScript-specific interpretation of the `(package, type)` tuple. */
API::Node getExtraNodeFromType(string type) {
  exists(string package, string qualifiedName |
    parseRelevantTypeString(type, package, qualifiedName)
  |
    qualifiedName = "" and
    result = packageNode(package)
    or
    // Access instance of a type based on type annotations
    result = API::Internal::getANodeOfTypeRaw(package, qualifiedName)
  )
  or
  result = getNodeFromValueAccessPath(type)
}

/**
 * Gets a JavaScript-specific API graph successor of `node` reachable by resolving `token`.
 */
bindingset[token]
API::Node getExtraSuccessorFromNode(API::Node node, AccessPathTokenBase token) {
  token.getName() = "Member" and
  result = node.getMember(token.getAnArgument())
  or
  token.getName() = "AnyMember" and
  result = node.getAMember()
  or
  token.getName() = "Instance" and
  result = node.getInstance()
  or
  token.getName() = "Awaited" and
  result = node.getPromised()
  or
  token.getName() = "ArrayElement" and
  result = node.getMember(DataFlow::PseudoProperties::arrayElement())
  or
  token.getName() = "Element" and
  result = node.getMember(DataFlow::PseudoProperties::arrayLikeElement())
  or
  // Note: MapKey not currently supported
  token.getName() = "MapValue" and
  result = node.getMember(DataFlow::PseudoProperties::mapValueAll())
  or
  // Currently we need to include the "unknown member" for ArrayElement and Element since
  // API graphs do not use store/load steps for arrays
  token.getName() = ["ArrayElement", "Element"] and
  result = node.getUnknownMember()
  or
  token.getName() = "Parameter" and
  token.getAnArgument() = "this" and
  result = node.getReceiver()
  or
  token.getName() = "DecoratedClass" and
  result = node.getADecoratedClass()
  or
  token.getName() = "DecoratedMember" and
  result = node.getADecoratedMember()
  or
  token.getName() = "DecoratedParameter" and
  result = node.getADecoratedParameter()
}

/**
 * Gets a JavaScript-specific API graph successor of `node` reachable by resolving `token`.
 */
bindingset[token]
API::Node getExtraSuccessorFromInvoke(API::InvokeNode node, AccessPathTokenBase token) {
  token.getName() = "Instance" and
  result = node.getInstance()
  or
  token.getName() = "Argument" and
  token.getAnArgument() = "this" and
  result.asSink() = node.(DataFlow::CallNode).getReceiver()
}

/**
 * Holds if `name` is the name of a built-in method on Object, Array, or String.
 */
private predicate isCommonBuiltinMethodName(string name) {
  exists(JS::ExternalInstanceMemberDecl member |
    member.getBaseName() in ["Object", "Array", "String"] and
    name = member.getName()
  )
}

/**
 * Holds if fuzzy evaluation should not traverse through `call`.
 */
private predicate blockFuzzyCall(DataFlow::CallNode call) {
  isCommonBuiltinMethodName(call.getCalleeName())
}

pragma[inline]
API::Node getAFuzzySuccessor(API::Node node) {
  result = node.getAMember() and
  // Block traversal into calls to built-ins like .toString() and .substring()
  // Since there is no API node representing the call itself, block flow into the callee node.
  not exists(DataFlow::CallNode call |
    node.asSource() = call.getCalleeNode() and
    blockFuzzyCall(call)
  )
  or
  result = node.getAParameter()
  or
  result = node.getReturn()
  or
  result = node.getPromised()
  or
  // include 'this' parameters but not 'this' arguments
  result = node.getReceiver() and result.asSource() instanceof DataFlow::ThisNode
}

/**
 * Holds if `invoke` matches the JS-specific call site filter in `token`.
 */
bindingset[token]
predicate invocationMatchesExtraCallSiteFilter(API::InvokeNode invoke, AccessPathTokenBase token) {
  token.getName() = "NewCall" and
  invoke instanceof API::NewNode
  or
  token.getName() = "Call" and
  invoke instanceof API::CallNode and
  invoke instanceof DataFlow::CallNode // Workaround compiler bug
  or
  token.getName() = "WithStringArgument" and
  exists(string operand, string argIndex, string stringValue |
    operand = token.getAnArgument() and
    argIndex = operand.splitAt("=", 0) and
    stringValue = operand.splitAt("=", 1) and
    invoke.getArgument(parseIntWithArity(argIndex, invoke.getNumArgument())).getStringValue() =
      stringValue
  )
}

/**
 * Holds if `path` is an input or output spec for a summary with the given `base` node.
 */
pragma[nomagic]
private predicate relevantInputOutputPath(API::InvokeNode base, AccessPath inputOrOutput) {
  exists(string type, string input, string output, string path |
    ModelOutput::relevantSummaryModel(type, path, input, output, _) and
    ModelOutput::resolvedSummaryBase(type, path, base) and
    inputOrOutput = [input, output]
  )
}

/**
 * Gets the API node for the first `n` tokens of the given input/output path, evaluated relative to `baseNode`.
 */
private API::Node getNodeFromInputOutputPath(API::InvokeNode baseNode, AccessPath path, int n) {
  relevantInputOutputPath(baseNode, path) and
  (
    n = 1 and
    result = getSuccessorFromInvoke(baseNode, path.getToken(0))
    or
    result =
      getSuccessorFromNode(getNodeFromInputOutputPath(baseNode, path, n - 1), path.getToken(n - 1))
  )
}

/**
 * Gets the API node for the given input/output path, evaluated relative to `baseNode`.
 */
private API::Node getNodeFromInputOutputPath(API::InvokeNode baseNode, AccessPath path) {
  result = getNodeFromInputOutputPath(baseNode, path, path.getNumToken())
}

/**
 * Holds if a CSV summary contributed the step `pred -> succ` of the given `kind`.
 */
predicate summaryStep(API::Node pred, API::Node succ, string kind) {
  exists(string type, string path, API::InvokeNode base, AccessPath input, AccessPath output |
    ModelOutput::relevantSummaryModel(type, path, input, output, kind) and
    ModelOutput::resolvedSummaryBase(type, path, base) and
    pred = getNodeFromInputOutputPath(base, input) and
    succ = getNodeFromInputOutputPath(base, output)
  )
}

class InvokeNode = API::InvokeNode;

/** Gets an `InvokeNode` corresponding to an invocation of `node`. */
InvokeNode getAnInvocationOf(API::Node node) { result = node.getAnInvocation() }

/**
 * Holds if `name` is a valid name for an access path token in the identifying access path.
 */
bindingset[name]
predicate isExtraValidTokenNameInIdentifyingAccessPath(string name) {
  name =
    [
      "Member", "AnyMember", "Instance", "Awaited", "ArrayElement", "Element", "MapValue",
      "NewCall", "Call", "DecoratedClass", "DecoratedMember", "DecoratedParameter",
      "WithStringArgument"
    ]
}

/**
 * Holds if `name` is a valid name for an access path token with no arguments, occurring
 * in an identifying access path.
 */
predicate isExtraValidNoArgumentTokenInIdentifyingAccessPath(string name) {
  name =
    [
      "AnyMember", "Instance", "Awaited", "ArrayElement", "Element", "MapValue", "NewCall", "Call",
      "DecoratedClass", "DecoratedMember", "DecoratedParameter"
    ]
}

/**
 * Holds if `argument` is a valid argument to an access path token with the given `name`, occurring
 * in an identifying access path.
 */
bindingset[name, argument]
predicate isExtraValidTokenArgumentInIdentifyingAccessPath(string name, string argument) {
  name = ["Member"] and
  exists(argument)
  or
  name = "WithStringArgument" and
  exists(argument.indexOf("=")) and
  exists(parseIntWithArity(argument.splitAt("=", 0), 10))
}

module ModelOutputSpecific {
  /**
   * Gets a node that should be seen as an instance of `package,type` due to a type definition
   * contributed by a CSV model.
   */
  cached
  API::Node getATypeNode(string package, string qualifiedName) {
    exists(string rawType |
      result = ModelOutput::getATypeNode(rawType) and
      parseTypeString(rawType, package, qualifiedName)
    )
  }
}
