private import All

private module SsaConfig implements Cfg::LanguageSsaSig {
  // All we need is exposed from the 'Variables' modules
  // TODO: Perhaps should factor this in a 'LanguageVariableSig' and not have an 'LanguageSsaSig'
  import codeql.js.common.Variables
}

module Ssa = Cfg::LanguageSsa<SsaConfig>;

private Ssa::WriteDefinition getSsaWriteNode(VariableReference def) {
  exists(Cfg::BasicBlock bb, int i |
    getLValueNode(def) = bb.getNode(i) and
    result.definesAt(def.getVariable(), bb, i)
  )
}

private Ssa::Definition getSsaReadNode(VariableReference ref) {
  exists(Cfg::BasicBlock bb, int i |
    ref = bb.getNode(i) and
    result.definesAt(ref.getVariable(), bb, i)
  )
}

predicate defUse(VariableReference def, VariableReference use) {
  exists(LocalVariable v, Ssa::Definition ssaDef, Cfg::BasicBlock bb, int i |
    Ssa::ssaDefReachesRead(v, ssaDef, bb, i) and
    ssaDef = getSsaWriteNode(def) and
    use = bb.getNode(i)
  )
}
