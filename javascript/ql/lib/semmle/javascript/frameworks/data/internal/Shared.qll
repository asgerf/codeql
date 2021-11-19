/**
 * INTERNAL use only. This is an experimental API subject to change without notice.
 *
 * Provides classes and predicates for dealing with flow models specified in CSV format.
 *
 * The CSV specification has the following columns:
 * - Sources:
 *   `package; type; path; kind`
 * - Sinks:
 *   `package; type; path; kind`
 * - Summaries:
 *   `package; type; path; input; output; kind`
 * - Types:
 *   `package1; type1; package2; type2; path`
 *
 * The interpretation of a row is similar to API-graphs with a left-to-right
 * reading.
 * 1. The `package` column selects an NPM package name, or "global" for the global scope.
 *    It may also be a path within an NPM package, such as `lodash/extend`.
 *    Lastly it can be a synthetic package used for a type definition (see type definitions below).
 * 2. The `type` column selects all instances of a named type originating from that package,
 *    or the empty string if referring to the package itself (its exported object).
 *    It can also be a synthetic type name defined by a type definition (see type definitions below).
 * 3. The `path` column API-graph-like edges to follow starting at the node selected by `package` and `type`.
 *    It is a `.`-separated list of tokens of form:
 *     - Member[x] : a property named `x`. May be a comma-separated list of named.
 *     - Argument[n]: the n-th argument to a call. May be a range of form `x-y` (inclusive) and/or a comma-separated list.
 *     - Parameter[n]: the n-th parameter of a callback. May be a range of form `x-y` (inclusive) and/or a comma-separated list.
 *     - ReturnValue: the value returned by a function call
 *     - Instance: the value returned by a constructor call
 *     - Awaited: the value from a resolved promise/future-like object
 *     - Other langauge-specific tokens mentioned in `ModelsAsData.qll`.
 * 4. The `input` and `output` columns specify how data enters and leaves the element selected by the
 *    first `(package, type, path)` tuple. Both strings are `.`-separated access paths
 *    of the same syntax as the `path` column.
 * 5. The `kind` column is a tag that can be referenced from QL to determine to
 *    which classes the interpreted elements should be added. For example, for
 *    sources `"remote"` indicates a default remote flow source, and for summaries
 *    `"taint"` indicates a default additional taint step and `"value"` indicates a
 *    globally applicable value-preserving step.
 *
 * ### Types
 *
 * A type row of form `package1; type1; package2; type2; path` indicates that `package2; type2; path`
 * should be seen as an instance of the type `package1; type1`.
 *
 * A `(package,type)` pair may refer to a static type or a synthetic type name used internally in the model.
 * Synthetic type names can be used to reuse intermediate sub-paths, when there are multiple ways to access the same
 * element.
 * See `ModelsAsData.qll` for the langauge-specific interpretation of packages and static type names.
 *
 * By convention, if one wants to avoid clashes with static types from the package, the type name
 * should be prefixed with a tilde character (`~`). For example, `(foo, ~Bar)` can be used to indicate that
 * the type is related to the `foo` package but is not intended to match a static type.
 */

private import Impl as Impl

private class Unit = Impl::Unit;

private module API = Impl::API;

/** Module containing hooks for providing input data to be interpreted as a model. */
module ModelInput {
  /**
   * A unit class for adding additional source model rows.
   *
   * Extend this class to add additional source definitions.
   */
  class SourceModelCsv extends Unit {
    /**
     * Holds if `row` specifies a source definition.
     *
     * A row of form
     * ```
     * package;type;path;kind
     * ```
     * indicates that the value at `(package, type, path)` should be seen as a flow
     * source of the given `kind`.
     *
     * The kind `remote` represents a general remote flow source.
     */
    abstract predicate row(string row);
  }

  /**
   * A unit class for adding additional sink model rows.
   *
   * Extend this class to add additional sink definitions.
   */
  class SinkModelCsv extends Unit {
    /**
     * Holds if `row` specifies a sink definition.
     *
     * A row of form
     * ```
     * package;type;path;kind
     * ```
     * indicates that the value at `(package, type, path)` should be seen as a sink
     * of the given `kind`.
     */
    abstract predicate row(string row);
  }

  /**
   * A unit class for adding additional summary model rows.
   *
   * Extend this class to add additional flow summary definitions.
   */
  class SummaryModelCsv extends Unit {
    /**
     * Holds if `row` specifies a summary definition.
     *
     * A row of form
     * ```
     * package;type;path;input;output;kind
     * ```
     * indicates that for each call to `(package, type, path)`, the value referred to by `input`
     * can flow to the value referred to by `output`.
     *
     * `kind` should be either `value` or `taint`, for value-preserving or taint-preserving steps,
     * respectively.
     */
    abstract predicate row(string row);
  }

  /**
   * A unit class for adding additional type model rows.
   *
   * Extend this class to add additional type definitions.
   */
  class TypeModelCsv extends Unit {
    /**
     * Holds if `row` specifies a type definition.
     *
     * A row of form,
     * ```
     * package1;type1;package2;type2;path
     * ```
     * indicates that `(package2, type2, path)` should be seen as an instance of `(package1, type1)`.
     */
    abstract predicate row(string row);
  }
}

private import ModelInput

/**
 * Append `;dummy` to the value of `s` to work around the fact that `string.split(delim,n)`
 * does not preserve empty trailing substrings.
 */
bindingset[result]
private string padded(string s) { s = result + ";dummy" }

private predicate sourceModel(string row) { any(SourceModelCsv s).row(padded(row)) }

private predicate sinkModel(string row) { any(SinkModelCsv s).row(padded(row)) }

private predicate summaryModel(string row) { any(SummaryModelCsv s).row(padded(row)) }

private predicate typeModel(string row) { any(TypeModelCsv s).row(padded(row)) }

/** Prefixes a non-empty path with `.` in order to simplify subsequent path-string manipulation. */
bindingset[path]
private string normalizePath(string path) {
  path = "" and result = ""
  or
  path != "" and
  result = "." + path
}

/** Holds if a source model exists for the given parameters. */
predicate sourceModel(string package, string type, string path, string kind) {
  exists(string row |
    sourceModel(row) and
    row.splitAt(";", 0) = package and
    row.splitAt(";", 1) = type and
    normalizePath(row.splitAt(";", 2)) = path and
    row.splitAt(";", 3) = kind
  )
}

/** Holds if a sink model exists for the given parameters. */
private predicate sinkModel(string package, string type, string path, string kind) {
  exists(string row |
    sinkModel(row) and
    row.splitAt(";", 0) = package and
    row.splitAt(";", 1) = type and
    normalizePath(row.splitAt(";", 2)) = path and
    row.splitAt(";", 3) = kind
  )
}

/** Holds if a summary model `row` exists for the given parameters. */
private predicate summaryModel(
  string package, string type, string path, string input, string output, string kind
) {
  exists(string row |
    summaryModel(row) and
    row.splitAt(";", 0) = package and
    row.splitAt(";", 1) = type and
    normalizePath(row.splitAt(";", 2)) = path and
    row.splitAt(";", 3) = input and
    row.splitAt(";", 4) = output and
    row.splitAt(";", 5) = kind
  )
}

/** Holds if an type model exists for the given parameters. */
private predicate typeModel(
  string package1, string type1, string package2, string type2, string path
) {
  exists(string row |
    typeModel(row) and
    row.splitAt(";", 0) = package1 and
    row.splitAt(";", 1) = type1 and
    row.splitAt(";", 2) = package2 and
    row.splitAt(";", 3) = type2 and
    normalizePath(row.splitAt(";", 4)) = path
  )
}

/**
 * Holds if CSV rows involving `package` might be relevant for the analysis of this database.
 */
private predicate isRelevantPackage(string package) {
  Impl::isPackageUsed(package)
  or
  exists(string other |
    isRelevantPackage(other) and
    typeModel(package, _, other, _, _)
  )
}

/**
 * Holds if `package,type,path` is used in some CSV row.
 */
pragma[nomagic]
predicate isRelevantFullPath(string package, string type, string path) {
  isRelevantPackage(package) and
  (
    sourceModel(package, type, path, _) or
    sinkModel(package, type, path, _) or
    summaryModel(package, type, path, _, _, _) or
    typeModel(_, _, package, type, path)
  )
}

/**
 * Holds if `path` or some suffix thereof is used with the `package,type` combination in some CSV row.
 */
pragma[nomagic]
private predicate isRelevantPath(string package, string type, string path) {
  exists(string fullPath |
    isRelevantFullPath(package, type, fullPath) and
    path = fullPath.prefix([fullPath.indexOf("."), fullPath.length()])
  )
}

/**
 * Gets a package that should be seen as an alias for the given other `package`,
 * or the `package` itself.
 */
bindingset[package]
bindingset[result]
string getAPackageAlias(string package) {
  typeModel(package, "", result, "", "")
  or
  result = package
}

/** Gets the API node corresponding to `(package, type, path)` from a CSV row. */
pragma[nomagic]
API::Node getNodeFromPath(string package, string type, string path) {
  isRelevantPath(package, type, path) and
  (
    type = "" and
    path = "" and
    result = API::moduleImport(package)
    or
    path = "" and
    exists(string package2, string type2, string path2 |
      typeModel(package, type, package2, type2, path2) and
      result = getNodeFromPath(package2, type2, path2)
    )
    or
    // Language-specific cases, such as handling of global variables
    result = Impl::getExtraNodeFromPath(package, type, path)
  )
  or
  // To get a good join order in the recursive case, scan the recursive delta, check the API graph
  // for outgoing edges, and then map those back to access path tokens, not the other way around.
  exists(API::Node baseNode, string base, string token |
    baseNode = getNodeFromPath(package, type, pragma[only_bind_into](base)) and
    result = baseNode.getASuccessor(getApiGraphLabelFromPathToken(pragma[only_bind_into](token))) and
    path = base + "." + token and
    isRelevantPath(package, type, pragma[only_bind_out](path))
  )
}

/**
 * Holds if a summary edge with the given `input, output, kind` columns have a `package, type, path` tuple
 * that resolves to `baseNode`.
 */
predicate resolvedSummaryBase(API::InvokeNode baseNode, string input, string output, string kind) {
  exists(string package, string type, string path |
    summaryModel(package, type, path, input, output, kind) and
    baseNode = getNodeFromPath(package, type, path).getAnInvocation()
  )
}

/**
 * Holds if `inputOrOutput` or some suffix thereof is used as the input or output part
 * of a summary edge using `base` as the base node.
 */
pragma[nomagic]
private predicate relevantInputOutputPath(API::InvokeNode base, string inputOrOutput) {
  exists(string baseIo | inputOrOutput = baseIo.prefix([0, baseIo.indexOf("."), baseIo.length()]) |
    resolvedSummaryBase(base, baseIo, _, _) or
    resolvedSummaryBase(base, _, baseIo, _)
  )
}

/**
 * Gets an API-graph successor for the given invocation.
 */
bindingset[label]
private API::Node getSuccessorFromInvoke(API::InvokeNode invoke, string label) {
  exists(int i |
    result = invoke.getParameter(i) and
    label = API::EdgeLabel::parameter(i)
  )
  or
  label = API::EdgeLabel::return() and
  result = invoke.getReturn()
  or
  label = API::EdgeLabel::instance() and
  result = invoke.getInstance()
}

/**
 * Gets the API node for the given input/output part, evaluated relative to `baseNode`, which corresponds to `package,type,path`.
 */
private API::Node getNodeFromInputOutputPath(API::InvokeNode baseNode, string inputOrOutput) {
  relevantInputOutputPath(baseNode, inputOrOutput) and
  (
    // For the base case we must go through the API::InvokeNode type to correctly
    // handle the case where the function reference has been moved into a local variable,
    // since different calls have the same base API node.
    result = getSuccessorFromInvoke(baseNode, getApiGraphLabelFromPathToken(inputOrOutput))
    or
    exists(string prefix, string token, API::Node prefixNode |
      prefixNode = getNodeFromInputOutputPath(baseNode, prefix) and
      inputOrOutput = prefix + "." + token and
      result = prefixNode.getASuccessor(getApiGraphLabelFromPathToken(token))
    )
  )
}

/**
 * Holds if `token` is a token used in an access path, that is,
 * either the `path`, `input`, or `output` part of a CSV row.
 */
private predicate isAccessPathToken(string token) {
  exists(string path |
    isRelevantFullPath(_, _, path) or
    summaryModel(_, _, _, path, _, _) or
    summaryModel(_, _, _, _, path, _)
  |
    token = path.splitAt(".")
  )
}

/**
 * Gets an API graph edge label corresponding to the given access path token.
 */
pragma[noinline]
private string getApiGraphLabelFromPathToken(string token) {
  isAccessPathToken(token) and
  (
    exists(string arg |
      // API graphs use the same label for arguments and parameters. An edge originating from a
      // use-node represents be an argument, and an edge originating from a def-node represents a parameter.
      // We just map both to the same thing.
      token = ["Argument[" + arg + "]", "Parameter[" + arg + "]"] and
      exists(string part | part = arg.splitAt(",") |
        result = API::EdgeLabel::parameterByStringIndex(part)
        or
        exists(string lo, string hi |
          lo = part.regexpCapture("(\\d+)-(\\d+)", 1) and
          hi = part.regexpCapture("(\\d+)-(\\d+)", 2) and
          result = API::EdgeLabel::parameter([lo.toInt() .. hi.toInt()])
        )
      )
      or
      token = "Member[" + arg + "]" and
      result = API::EdgeLabel::member(arg.splitAt(","))
    )
    or
    token = "ReturnValue" and
    result = API::EdgeLabel::return()
    or
    // Language-specific tokens
    result = Impl::getExtraApiGraphLabelFromPathToken(token)
  )
}

/**
 * Module providing access  to the imported models in terms of API graph nodes.
 */
module ModelOutput {
  /**
   * Holds if a CSV source model contributed `source` with the given `kind`.
   */
  API::Node getASourceNode(string kind) {
    exists(string package, string type, string path |
      sourceModel(package, type, path, kind) and
      result = getNodeFromPath(package, type, path)
    )
  }

  /**
   * Holds if a CSV sink model contributed `sink` with the given `kind`.
   */
  API::Node getASinkNode(string kind) {
    exists(string package, string type, string path |
      sinkModel(package, type, path, kind) and
      result = getNodeFromPath(package, type, path)
    )
  }

  /**
   * Holds if a CSV summary contributed the step `pred -> succ` of the given `kind`.
   */
  predicate summaryStep(API::Node pred, API::Node succ, string kind) {
    exists(API::InvokeNode base, string input, string output |
      resolvedSummaryBase(base, input, output, kind) and
      pred = getNodeFromInputOutputPath(base, input) and
      succ = getNodeFromInputOutputPath(base, output)
    )
  }

  /**
   * Holds if `node` is seen as an instance of `(package,type)` due to a type definition
   * contributed by a CSV model.
   */
  API::Node getATypeNode(string package, string type) {
    exists(string package2, string type2, string path |
      typeModel(package, type, package2, type2, path) and
      result = getNodeFromPath(package2, type2, path)
    )
  }
}
