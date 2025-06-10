/**
 * Detects code that is specific to the brower environment.
 */

private import javascript

private predicate isBrowserSpecificTopLevel(TopLevel top) {
  exists(GlobalVarAccess access |
    access.getTopLevel() = top and
    access.getName() = ["document", "window"]
  )
  or
  top.getFile() instanceof Vue::VueFile
  or
  top = any(ReactComponent c).getTopLevel()
  or
  top = any(Angular2::ComponentClass c).getTopLevel()
  or
  top = any(AngularJS::ComponentDefinition s).getTopLevel()
  or
  exists(Import imprt |
    top = imprt.getTopLevel() and
    imprt.getImportedPathString() = ["global/window", "global/document", "jquery", "react-dom"]
  )
  or
  top instanceof JavaScriptUrl
  or
  top instanceof InlineScript
  or
  top instanceof EventHandlerCode
}

private predicate dependsOnBrowserSpecificTopLevel(TopLevel top) {
  isBrowserSpecificTopLevel(top)
  or
  dependsOnBrowserSpecificTopLevel(top.(Module).getAnImportedModule())
}

private predicate hasOwnExplicitServerContext(StmtContainer node, boolean server) {
  node.getAStmt() instanceof Directive::UseServerDirective and server = true
  or
  node.getAStmt() instanceof Directive::UseClientDirective and server = false
}

private predicate hasExplicitServerContext(StmtContainer node, boolean server) {
  hasOwnExplicitServerContext(node, server)
  or
  not hasOwnExplicitServerContext(node, _) and
  hasExplicitServerContext(node.getEnclosingContainer(), server)
}

/**
 * Holds if the given `container` appears to be specific to the browser environment.
 *
 * This is an under-approximation. That is, in cases of doubt, a container is not
 * considered to be in browser context.
 */
predicate isInBrowserContext(StmtContainer container) {
  dependsOnBrowserSpecificTopLevel(container.getTopLevel()) and
  not hasExplicitServerContext(container, _)
  or
  hasExplicitServerContext(container, false)
}
