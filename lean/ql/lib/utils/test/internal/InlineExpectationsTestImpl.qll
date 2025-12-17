private import codeql.js.base.GeneratedAst
private import codeql.Locations as L
private import codeql.util.test.InlineExpectationsTest

module Impl implements InlineExpectationsTestSig {
  /**
   * A class representing line comments in JS.
   */
  class ExpectationComment extends JS::Comment {
    string getContents() { result = this.getValue().regexpReplaceAll("^//|^/\\*|\\*/$", "") }
  }

  class Location = L::Location;
}
