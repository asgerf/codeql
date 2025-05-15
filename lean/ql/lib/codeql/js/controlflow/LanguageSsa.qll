private import All

private module SsaConfig implements Cfg::LanguageSsaSig {
  import codeql.js.common.Variables

  AstNode getClosureExprFromNestedCallable(CfgScope callable) {
    result = callable and
    not callable instanceof Program
    // TODO: map class constructors to their class
  }
}

module Ssa = Cfg::LanguageSsa<SsaConfig>;
