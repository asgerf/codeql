private import codeql.util.Location
private import codeql.util.Unit
private import LanguageBase
private import LanguageCommon
private import LanguageCfg
private import codeql.ssa.Ssa as Ssa

signature module LanguageSsaSig<
  LocationSig Location, LanguageBaseSig<Location> Base, LanguageCommonSig<Location, Base> Common,
  LanguageCfgBuilder<Location, Base, Common>::LanguageCfgSig CfgInput>
{
  class VariableReference extends Base::AstNode;

  class LocalVariable {
    VariableReference getAReference();

    string toString();

    Location getLocation();

    Common::CfgScope getCfgScope();

    predicate isCaptured();
  }

  default predicate assignmentIsUncertain(Base::SyntheticNode lvalueNode) { none() }

  default predicate readIsUncertain(VariableReference ref) { none() }

  default predicate definitelyInitialized(LocalVariable v) { none() }
}

module LanguageSsa<
  LocationSig Location, LanguageBaseSig<Location> Base, LanguageCommonSig<Location, Base> Common,
  LanguageCfgBuilder<Location, Base, Common>::LanguageCfgSig CfgInput,
  LanguageSsaSig<Location, Base, Common, CfgInput> LanguageSsaInput>
{
  private import Base
  private import Common
  private import CfgInput
  private import LanguageSsaInput
  private import MakeLanguageBase<Location, Base>
  private import MakeLanguageCommon<Location, Base, Common>
  private import LanguageCfgBuilder<Location, Base, Common>::MakeLanguageCfg<CfgInput>

  private class Node = AstNode;

  private module NonCapturedSsaConfig implements Ssa::InputSig<Location> {
    class BasicBlock = BasicBlocks::BasicBlock;

    class ControlFlowNode = AstNode;

    BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) { result.immediatelyDominates(bb) }

    BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

    final private class FinalLocalVariable = LocalVariable;

    class SourceVariable extends FinalLocalVariable {
      SourceVariable() { not this.isCaptured() }
    }

    pragma[nomagic]
    private BasicBlock getEntryBlock(CfgScope scope) { result.getANode() = getCfgEntryPoint(scope) }

    predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      exists(Node lvalueNode |
        lvalueNode = getLValueNode(v.getAReference()) and
        bb.getNode(i) = lvalueNode and
        if assignmentIsUncertain(lvalueNode) then certain = false else certain = true
      )
      or
      // For variables that are not definitely initialized, put a synthetic initializer in the entry block
      not definitelyInitialized(v) and
      bb = getEntryBlock(v.getCfgScope()) and
      i = -1 and
      certain = true
    }

    predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      exists(Node ref |
        ref = v.getAReference() and
        not isInPureLValuePosition(ref) and // not a read if pure lvalue
        bb.getNode(i) = ref and
        if readIsUncertain(ref) then certain = false else certain = true
      )
    }
  }

  import Ssa::Make<Location, NonCapturedSsaConfig>
}
