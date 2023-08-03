import javascript
private import semmle.javascript.dataflow2.DataFlow as DataFlow2
private import semmle.javascript.dataflow2.TaintTracking as TaintTracking2
private import semmle.javascript.dataflow2.BarrierGuards

module TestDataFlowConfigurationArgs implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow::Node src) {
    exists(VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getName().matches("%source%") and
      src.asExpr() = vd.getInit()
    )
  }

  predicate isSink(DataFlow::Node snk) {
    exists(VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getName().matches("%sink%") and
      snk.asExpr() = vd.getInit()
    )
  }

  predicate isBarrier(DataFlow::Node node) {
    exists(Function f |
      f.getName().matches("%noReturnTracking%") and
      node = f.getAReturnedExpr().flow()
    )
    or
    node.asExpr().(PropAccess).getPropertyName() = "notTracked"
    or
    barrierGuardBlocksNode(_, node, DataFlow::FlowLabel::data())
  }
}

module TestDataFlowConfiguration = DataFlow2::Global<TestDataFlowConfigurationArgs>;

query predicate dataFlow(DataFlow::Node src, DataFlow::Node snk) {
  TestDataFlowConfiguration::flow(src, snk)
}

class Parity extends DataFlow::FlowLabel {
  Parity() { this = "even" or this = "odd" }

  Parity flip() { result != this }
}

module FlowLabelConfigArg implements DataFlow2::StateConfigSig {
  class FlowState = DataFlow::FlowLabel;

  predicate isSource(DataFlow::Node nd, FlowState lbl) {
    nd.(DataFlow::CallNode).getCalleeName() = "source" and
    lbl = "even"
  }

  predicate isSink(DataFlow::Node nd, FlowState lbl) {
    nd = any(DataFlow::CallNode c | c.getCalleeName() = "sink").getAnArgument() and
    lbl = "even"
  }

  predicate isBarrier(DataFlow::Node node, FlowState state) {
    barrierGuardBlocksNode(_, node, state)
  }

  predicate isAdditionalFlowStep(
    DataFlow::Node pred, FlowState predLabel, DataFlow::Node succ, FlowState succLabel
  ) {
    exists(DataFlow::CallNode c | c = succ |
      c.getCalleeName() = "inc" and
      pred = c.getAnArgument() and
      succLabel = predLabel.(Parity).flip()
    )
  }
}

module FlowLabelConfig = DataFlow2::GlobalWithState<FlowLabelConfigArg>;

query predicate flowLabels(FlowLabelConfig::PathNode source, FlowLabelConfig::PathNode sink) {
  FlowLabelConfig::flowPath(source, sink)
}

module TestTaintTrackingConfigurationArg implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow::Node src) {
    exists(VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getName().matches("%source%") and
      src.asExpr() = vd.getInit()
    )
  }

  predicate isSink(DataFlow::Node snk) {
    exists(VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getName().matches("%sink%") and
      snk.asExpr() = vd.getInit()
    )
  }

  predicate isBarrier(DataFlow::Node node) {
    exists(Function f |
      f.getName().matches("%noReturnTracking%") and
      node = f.getAReturnedExpr().flow()
    )
    or
    node.asExpr().(PropAccess).getPropertyName() = "notTracked"
    or
    barrierGuardBlocksNode(_, node, DataFlow::FlowLabel::taint())
  }
}

module TestTaintTrackingConfiguration = TaintTracking2::Global<TestTaintTrackingConfigurationArg>;

query predicate taintTracking(DataFlow::Node src, DataFlow::Node snk) {
  TestTaintTrackingConfiguration::flow(src, snk)
}

module GermanFlowConfigArg implements DataFlow2::ConfigSig {
  predicate isSource(DataFlow::Node src) {
    exists(VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getName().matches("%source%") and
      src.asExpr() = vd.getInit()
    )
    or
    src.asExpr() = any(Variable v | v.getName() = "quelle").getAnAssignedExpr()
  }

  predicate isSink(DataFlow::Node snk) {
    exists(VariableDeclarator vd |
      vd.getBindingPattern().(VarDecl).getName().matches("%sink%") and
      snk.asExpr() = vd.getInit()
    )
    or
    snk.asExpr() = any(Variable v | v.getName() = "abfluss").getAnAssignedExpr()
  }

  predicate isBarrier(DataFlow::Node node) {
    exists(Function f |
      f.getName().matches("%noReturnTracking%") and
      node = f.getAReturnedExpr().flow()
    )
    or
    node.asExpr().(PropAccess).getPropertyName() = "notTracked"
    or
    barrierGuardBlocksNode(_, node, DataFlow::FlowLabel::data())
  }
}

module GermanFlowConfig = DataFlow2::Global<GermanFlowConfigArg>;

query predicate germanFlow(DataFlow::Node src, DataFlow::Node snk) {
  GermanFlowConfig::flow(src, snk)
}
