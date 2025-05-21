module JS {
  private import GeneratedAst::JS as G
  // This module re-exports the generated AST, shadowing the classes we have a facade for.
  // The generated AST refers to this module when referencing a type name, so predicates
  // have a more useful return type.
  import G

  /**
   * A compound assignment such as `x += e`.
   */
  class AugmentedAssignmentExpression extends G::AugmentedAssignmentExpression {
    /**
     * Gets a synthetic `binary-operator` node that represents the binary expression in the augmented assignment.
     */
    SyntheticNode getBinaryOperatorNode() { result = this.getSyntheticChildNode("binary-operator") }
  }

  /**
   * A `for (... in ...)` or `for (... of ...)` statement.
   */
  class ForInStatement extends G::ForInStatement {
    /**
     * Gets a synthetic `loop-header` node that represents the condition within the for-in loop.
     */
    SyntheticNode getLoopHeader() { result = this.getSyntheticChildNode("loop-header") }
  }

  final private class FinalForStatement = G::ForStatement;

  /**
   * A `for` statement.
   */
  class ForStatement extends FinalForStatement {
    /** Gets the loop condition or a synthetic `empty-condition` node if the condition was omitted. */
    AstNode getConditionOrEmptyNode() {
      result = super.getCondition(0)
      or
      result = this.getSyntheticChildNode("empty-condition")
    }

    /** Gets the increment expression or a synthetic `empty-increment` node if the increment was omitted. */
    AstNode getIncrementOrEmptyNode() {
      result = super.getIncrement()
      or
      result = this.getSyntheticChildNode("empty-increment")
    }
  }

  abstract private class ImportOrExportStatementImpl extends Statement {
    /** Gets a synthetic node representing the imported module. */
    SyntheticNode getImportedModuleNode() { result = this.getSyntheticChildNode("imported-module") }
  }

  final class ImportOrExportStatement = ImportOrExportStatementImpl;

  class ImportStatement extends G::ImportStatement, ImportOrExportStatementImpl {
    ImportClause getImportClause() { result = this.getChild(_) }

    /** Gets a `NamspaceImport`, `ImportSpecifier` or `Identifier` (for default import). */
    AstNode getASpecifier() {
      result = this.getImportClause().getDefaultImport()
      or
      result = this.getImportClause().getAsNamespaceImport()
      or
      result = this.getImportClause().getAsNamedImports().getChild(_)
    }
  }

  class ExportStatement extends G::ExportStatement, ImportOrExportStatementImpl { }

  class ImportClause extends G::ImportClause {
    Identifier getDefaultImport() { result = this.getChild(_) }

    NamespaceImport getAsNamespaceImport() { result = this.getChild(_) }

    NamedImports getAsNamedImports() { result = this.getChild(_) }
  }

  class Array extends G::Array {
    /** Gets the index of the first spread element in this array literal, if any. */
    int getFirstSpreadIndex() { result = min(int i | this.getChild(i) instanceof SpreadElement) }
  }

  class ImportSpecifier extends G::ImportSpecifier {
    /** Gets the `v` in `import { x as v }` or in `import { v }`. */
    AstNode getLocalName() {
      result = this.getAlias()
      or
      not exists(this.getAlias()) and
      result = this.getName()
    }
  }

  class CallExpression extends G::CallExpression {
    /** Gets the `n`th argument, where spread arguments are counted as a single element. */
    AstNode getArgument(int n) { result = this.getArguments().(Arguments).getChild(n) }

    /** Gets the index of the first spread argument in this call, if any. */
    int getFirstSpreadIndex() { result = min(int i | this.getArgument(i) instanceof SpreadElement) }
  }
}
