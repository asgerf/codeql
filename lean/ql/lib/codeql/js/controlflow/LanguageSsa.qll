private import All

private module SsaConfig implements Cfg::LanguageSsaSig {
  import codeql.js.common.Variables
}

module Ssa = Cfg::LanguageSsa<SsaConfig>;
