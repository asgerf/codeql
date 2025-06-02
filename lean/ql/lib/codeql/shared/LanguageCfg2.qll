private import codeql.Locations
private import codeql.util.Unit

signature class AstNodeSig {
  string toString();

  Location getLocation();
}

module LanguageCfg2<AstNodeSig AstNode> {
  bindingset[this]
  signature class CfgNodeSig {
    bindingset[node]
    predicate isBefore(AstNode node);

    bindingset[node]
    predicate isAfter(AstNode node);

    bindingset[node]
    predicate isBeforeAssigningTo(AstNode node);

    bindingset[node]
    predicate isAfterAssigningTo(AstNode node);
  }

  class UnitCfgNode extends Unit {
    bindingset[node]
    predicate isBefore(AstNode node) { any() }

    bindingset[node]
    predicate isAfter(AstNode node) { any() }

    bindingset[node]
    predicate isBeforeAssigningTo(AstNode node) { any() }

    bindingset[node]
    predicate isAfterAssigningTo(AstNode node) { any() }
  }

  final private class FinalAstNode = AstNode;

  final private class InferBaseNode extends FinalAstNode {
    bindingset[node]
    predicate isBefore(AstNode node) { none() }

    bindingset[node]
    predicate isAfter(AstNode node) { none() }

    bindingset[node]
    predicate isBeforeAssigningTo(AstNode node) { none() }

    bindingset[node]
    predicate isAfterAssigningTo(AstNode node) { none() }
  }

  class InferBeforeNode extends InferBaseNode {
    bindingset[node]
    predicate isBefore(AstNode node) { this = node }
  }

  class InferLValueNode extends InferBaseNode {
    bindingset[node]
    predicate isBeforeAssigningTo(AstNode node) { this = node }
  }

  signature predicate inferBeforeStep1(InferBeforeNode node1, UnitCfgNode node2);

  signature predicate inferBeforeStep2(UnitCfgNode node1, InferBeforeNode node2);

  module InferBefore<inferBeforeStep1/2 step1, inferBeforeStep2/2 step2> {
    predicate needsBeforeNode(AstNode node) { step1(node, _) or step2(_, node) }
  }

  signature predicate inferLValueStep(InferLValueNode node1, UnitCfgNode node2);

  module InferLValue<inferLValueStep/2 step> {
    predicate needsLValueNode(AstNode node) { step(node, _) }
  }

  signature predicate nodeSet(AstNode node);

  signature predicate nodeParentSig(AstNode parent, AstNode child, int index);

  module MakeCfg1<nodeSet/1 needsBefore, nodeSet/1 needsLValue, nodeParentSig/3 nodeParent> {
    private newtype TCfgNode =
      MkAfterNode(AstNode node) or
      MkBeforeNode(AstNode node) { needsBefore(node) } or
      MkBeforeAssignmentNode(AstNode node) { needsLValue(node) } or
      MkAfterAssignmentNode(AstNode node) { needsLValue(node) }

    class CfgNode extends TCfgNode {
      bindingset[node]
      predicate isBefore(AstNode node) { this = MkBeforeNode(node) }

      bindingset[node]
      predicate isAfter(AstNode node) { this = MkAfterNode(node) }

      bindingset[node]
      predicate isBeforeAssigningTo(AstNode node) { this = MkBeforeAssignmentNode(node) }

      bindingset[node]
      predicate isAfterAssigningTo(AstNode node) { this = MkAfterAssignmentNode(node) }

      string toString() {
        exists(AstNode node |
          this.isBefore(node) and result = "before " + node.toString()
          or
          this.isAfter(node) and result = node.toString()
          or
          this.isBeforeAssigningTo(node) and result = "before assigning to " + node.toString()
          or
          this.isAfterAssigningTo(node) and result = "after assigning to " + node.toString()
        )
      }

      Location getLocation() {
        exists(AstNode node |
          this.isBefore(node) or
          this.isAfter(node) or
          this.isBeforeAssigningTo(node) or
          this.isAfterAssigningTo(node)
        |
          result = node.getLocation()
        )
      }
    }

    signature predicate stepSig(CfgNode node1, CfgNode node2);

    module MakeCfg2<stepSig/2 explicitStep> { }
  }
}
