private import codeql.util.Location
private import codeql.util.Unit
private import LanguageBase
private import LanguageCommon
private import LanguageCfg

signature module ContentSpecSig {
  /**
   * Holds if a MaD token with `head` is valid, and whether it can accept an operand.
   *
   * This is in addition to the built-in tokens:
   * - `Argument`, `Parameter`, `ReturnValue`
   *
   * `operand` should be empty for a token without any operand.
   */
  predicate isValidContentHead(string head, string operand);

  /**
   * A language-specific content with no MaD token.
   */
  class SpecificContent;
}

module LanguageDataflowBuilder<
  LocationSig Location, LanguageBaseSig<Location> B, LanguageCommonSig<Location, B> C,
  ContentSpecSig ContentSpec>
{
  private import B
  private import C

  private class Node = AstNode;

  /**
   * Flow steps contributed to stage 1.
   */
  class Stage1 extends Unit {
    predicate valueStep(Node node1, Node node2) { none() }

    predicate taintStep(Node node1, Node node2) { none() }

    predicate readStep(Node node1, ContentSet contents, Node node2) { none() }

    predicate storeStep(Node node1, ContentSet contents, Node node2) { none() }

    predicate clearsContent(Node node1, ContentSet contents) { none() }

    predicate expectsContent(Node node1, ContentSet contents) { none() }
  }

  /**
   * Gets the entry point of the given CFG scope.
   */
  pragma[nomagic]
  CfgNode getCfgEntryPoint(CfgScope scope) { result = scope.getFirstNode() }
}

signature module LanguageSsaSig {
  class LocalVariable {
    VariableReference getAReference();

    string toString();

    Location getLocation();

    CfgScope getCfgScope();

    predicate isCaptured();
  }

  class VariableReference extends Node;

  default predicate assignmentIsUncertain(L::SyntheticNode lvalueNode) { none() }

  default predicate readIsUncertain(VariableReference ref) { none() }

  default predicate definitelyInitialized(LocalVariable v) { none() }
}

module LanguageSsa<LanguageSsaSig LanguageSsaInput> {
  private import LanguageSsaInput

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
