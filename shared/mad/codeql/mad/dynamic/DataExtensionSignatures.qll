/**
 * Provides a signature module for the data extensions used in dynamic MaD.
 */

/**
 * Contains the signatures of the data extensions used in dynamic MaD.
 */
signature module DataExtensionsSig {
  /**
   * Holds if the value at `(type, path)` should be seen as a flow
   * source of the given `kind` and `madId` is the data extension row number.
   *
   * The kind `remote` represents a general remote flow source.
   */
  predicate sourceModel(string type, string path, string kind, QlBuiltins::ExtensionId madId);

  /**
   * Holds if the value at `(type, path)` should be seen as a sink
   * of the given `kind` and `madId` is the data extension row number.
   */
  predicate sinkModel(string type, string path, string kind, QlBuiltins::ExtensionId madId);

  /**
   * Holds if the value at `(type, path)` should be seen as a barrier
   * of the given `kind` and `madId` is the data extension row number.
   */
  predicate barrierModel(string type, string path, string kind, QlBuiltins::ExtensionId madId);

  /**
   * Holds if the value at `(type, path)` should be seen as a barrier guard
   * of the given `kind` and `madId` is the data extension row number.
   * `path` is assumed to lead to a parameter of a call (possibly `self`), and
   * the call is guarding the parameter.
   * `branch` is either `true` or `false`, indicating which branch of the guard
   * is protecting the parameter.
   */
  predicate barrierGuardModel(
    string type, string path, string branch, string kind, QlBuiltins::ExtensionId madId
  );

  /**
   * Holds if in calls to `(type, path)`, the value referred to by `input`
   * can flow to the value referred to by `output` and `madId` is the data
   * extension row number.
   *
   * `kind` should be either `value` or `taint`, for value-preserving or taint-preserving steps,
   * respectively.
   */
  predicate summaryModel(
    string type, string path, string input, string output, string kind,
    QlBuiltins::ExtensionId madId
  );

  /**
   * Holds if calls to `(type, path)` should be considered neutral. The meaning of this depends on the `kind`.
   * If `kind` is `summary`, the call does not propagate data flow. If `kind` is `source`, the call is not a source.
   * If `kind` is `sink`, the call is not a sink.
   */
  predicate neutralModel(string type, string path, string kind);

  /**
   * Holds if `(type2, path)` should be seen as an instance of `type1`.
   */
  predicate typeModel(string type1, string type2, string path);

  /**
   * Holds if `path` can be substituted for a token `TypeVar[name]`.
   */
  predicate typeVariableModel(string name, string path);
}
