private import javascript as js
private import semmle.javascript.dataflow.internal.DataFlowNode
private import DataFlowImplSpecific::Private
private import DataFlowImplSpecific::Public
private import codeql.dataflow.VariableCapture

private js::Function getLambdaFromVariable(js::LocalVariable variable) {
  result.getVariable() = variable
  or
  result = variable.getAnAssignedExpr()
  or
  exists(js::ClassDeclStmt cls |
    result = cls.getConstructor().getBody() and
    variable = cls.getVariable()
  )
}

predicate captures(js::Function fun, js::LocalVariable variable) {
  (
    variable.getAnAccess().getContainer().getFunctionBoundary() = fun
    or
    exists(js::Function inner |
      captures(inner, variable) and
      fun = inner.getEnclosingContainer().getFunctionBoundary()
    )
    or
    // if capturing another function, include the captures of that function
    exists(js::LocalVariable otherLambdaVar |
      captures(fun, otherLambdaVar) and
      captures(getLambdaFromVariable(otherLambdaVar), variable)
    )
  ) and
  not variable.getDeclaringContainer() = fun
}

private module VariableCaptureArg implements InputSig {
  class BasicBlock extends js::BasicBlock {
    Callable getEnclosingCallable() { result = this.getContainer().getFunctionBoundary() }
  }

  class Location = js::Location;

  class Callable extends js::StmtContainer {
    predicate isConstructor() {
      // TODO: clarify exactly what the library wants to know here as the meaning of "constructor" varies between languages.
      // I believe JS constructors should not be seen as "constructors" in this context, because the 'this' parameter
      // is different from the function self-reference parameter. For the purpose of capturing, constructors are not special.
      none()
    }
  }

  class CapturedVariable extends js::LocalVariable {
    CapturedVariable() {
      this.isCaptured() and
      not exists(getLambdaFromVariable(this))
      // TODO: exclude top-level variables as they are singletons, and can safely be modelled with jump steps
    }

    Callable getCallable() { result = this.getDeclaringContainer().getFunctionBoundary() }
  }

  class CapturedParameter extends CapturedVariable {
    CapturedParameter() { this.isParameter() }
  }

  class Expr extends js::AST::ValueNode {
    /** Holds if the `i`th node of basic block `bb` evaluates this expression. */
    predicate hasCfgNode(BasicBlock bb, int i) {
      // Note: this is overridden for FunctionDeclStmt
      bb.getNode(i) = this
    }
  }

  private class FunctionDeclStmtAsExpr extends Expr, js::FunctionDeclStmt {
    override predicate hasCfgNode(BasicBlock bb, int i) {
      // All FunctionDeclStmts are evaluated at index 0, where all implicit inits have already occurred (at index -1)
      // but their corresponding VariableWrites have not yet occurred.
      i = 0 and bb = this.getEnclosingContainer().getEntryBB()
    }
  }

  class VariableRead extends Expr instanceof js::VarAccess, js::RValue {
    private CapturedVariable variable;

    VariableRead() { this = variable.getAnAccess() }

    CapturedVariable getVariable() { result = variable }
  }

  private predicate readBB(VariableRead read, BasicBlock bb, int i) { read.hasCfgNode(bb, i) }

  private predicate writeBB(VariableWrite write, BasicBlock bb, int i) { write.hasCfgNode(bb, i) }

  class ClosureExpr extends Expr {
    ClosureExpr() { captures(this, _) }

    predicate hasBody(Callable c) { c = this }

    predicate hasAliasedAccess(Expr e) {
      e = this
      or
      exists(js::LocalVariable variable |
        this = getLambdaFromVariable(variable) and
        e = variable.getAnAccess()
      )
    }
  }

  private newtype TVariableWrite =
    MkExplicitVariableWrite(js::VarRef pattern) {
      exists(js::DataFlow::lvalueNodeInternal(pattern)) and
      pattern.getVariable() instanceof CapturedVariable
    } or
    MkImplicitVariableInit(CapturedVariable v) { not v instanceof CapturedParameter }

  class VariableWrite extends TVariableWrite {
    CapturedVariable getVariable() { none() } // Overridden in subclass

    string toString() { none() } // Overridden in subclass

    Location getLocation() { none() } // Overridden in subclass

    predicate hasCfgNode(BasicBlock bb, int i) { none() } // Overridden in subclass

    // note: langauge-specific
    js::DataFlow::Node getSource() { none() } // Overridden in subclass
  }

  additional class ExplicitVariableWrite extends VariableWrite, MkExplicitVariableWrite {
    private js::VarRef pattern;

    ExplicitVariableWrite() { this = MkExplicitVariableWrite(pattern) }

    override CapturedVariable getVariable() { result = pattern.getVariable() }

    override string toString() { result = pattern.toString() }

    /** Gets the location of this write. */
    override Location getLocation() { result = pattern.getLocation() }

    override js::DataFlow::Node getSource() {
      // Note: there is not always an expression corresponding to the RHS of the assignment.
      // We do however have a data-flow node for this purpose (the lvalue-node).
      // We use the pattern as a placeholder here, to be mapped to a data-flow node with `DataFlow::lvalueNode`.
      result = js::DataFlow::lvalueNodeInternal(pattern)
    }

    /** Holds if the `i`th node of basic block `bb` evaluates this expression. */
    override predicate hasCfgNode(BasicBlock bb, int i) {
      bb.getNode(i) = pattern.(js::LValue).getDefNode()
    }
  }

  additional class ImplicitVariableInit extends VariableWrite, MkImplicitVariableInit {
    private CapturedVariable variable;

    ImplicitVariableInit() { this = MkImplicitVariableInit(variable) }

    override string toString() { result = "[implicit init] " + variable }

    override Location getLocation() { result = variable.getLocation() }

    override CapturedVariable getVariable() { result = variable }

    override predicate hasCfgNode(BasicBlock bb, int i) {
      // 'i' would normally be bound to 0, but we lower it to -1 so FunctionDeclStmts can be evaluated
      // at index 0.
      any(js::SsaImplicitInit def).definesAt(bb, _, variable) and i = -1
    }
  }

  BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

  BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) { result = bb.getImmediateDominator() }

  predicate entryBlock(BasicBlock bb) { bb instanceof js::EntryBasicBlock }

  predicate exitBlock(BasicBlock bb) { bb.getLastNode() instanceof js::ControlFlowExitNode }
}

module VariableCaptureOutput = Flow<VariableCaptureArg>;

predicate missingNode(VariableCaptureOutput::ClosureNode closureNode) {
  not exists(getNodeFromClosureNode(closureNode)) and
  (
    VariableCaptureOutput::localFlowStep(closureNode, _)
    or
    VariableCaptureOutput::localFlowStep(_, closureNode)
  )
}

js::DataFlow::Node getNodeFromClosureNode(VariableCaptureOutput::ClosureNode node) {
  result = TValueNode(node.(VariableCaptureOutput::ExprNode).getExpr())
  or
  result = TValueNode(node.(VariableCaptureOutput::ParameterNode).getParameter().getADeclaration()) // TODO: is this subsumed by the ExprNode case?
  or
  result = TExprPostUpdateNode(node.(VariableCaptureOutput::ExprPostUpdateNode).getExpr())
  or
  // Note: the `this` parameter in the capture library is expected to be a parameter that refers to the lambda object itself,
  // which for JS means the `TFunctionSelfReferenceNode`, not `TThisNode` as one might expect.
  result = TFunctionSelfReferenceNode(node.(VariableCaptureOutput::ThisParameterNode).getCallable())
  or
  result = TSynthCaptureNode(node.(VariableCaptureOutput::SynthesizedCaptureNode))
  or
  result = node.(VariableCaptureOutput::VariableWriteSourceNode).getVariableWrite().getSource()
  // or
  // result = TConstructorThisArgumentNode(node.(VariableCaptureOutput::MallocNode).getClosureExpr())
}

VariableCaptureOutput::ClosureNode getClosureNode(js::DataFlow::Node node) {
  node = getNodeFromClosureNode(result)
}

module Debug {
  predicate relevantContainer(js::StmtContainer container) {
    container.getEnclosingContainer*().(js::Function).getName() = "exists"
  }

  predicate localFlowStep(
    VariableCaptureOutput::ClosureNode node1, VariableCaptureOutput::ClosureNode node2
  ) {
    VariableCaptureOutput::localFlowStep(node1, node2)
  }

  predicate localFlowStepMapped(js::DataFlow::Node node1, js::DataFlow::Node node2) {
    localFlowStep(getClosureNode(node1), getClosureNode(node2)) and
    relevantContainer(node1.getContainer())
  }
}
