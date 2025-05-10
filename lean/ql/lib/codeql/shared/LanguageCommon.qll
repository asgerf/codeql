private import codeql.util.Location
private import codeql.shared.LanguageBase

signature module LanguageCommonSig<LocationSig Location, LanguageBaseSig<Location> L> {
  class CfgScope extends L::AstNode;

  CfgScope getCfgScope(L::AstNode node);
}
