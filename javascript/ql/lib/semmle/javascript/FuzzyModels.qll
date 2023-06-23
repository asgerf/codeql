private import javascript

private DataFlow::SourceNode blockedNode() {
  exists(string name | name = result.(DataFlow::PropRead).getPropertyName() |
    name =
      any(ExternalInstanceMemberDecl decl | decl.getBaseName() = ["Object", "String", "Array"])
          .getName()
    or
    name = ["then", "catch", "finally"]
  )
  or
  exists(API::AdditionalUseStep step | step.step(_, result))
  or
  DataFlow::SharedFlowStep::step(_, result)
}

/**
 * Gets a normalized package name from `importString`.
 */
bindingset[importString]
string normalizePackageName(string importString) {
  result =
    importString
        .regexpReplaceAll("^node:", "")
        .regexpReplaceAll("\\.js$", "")
        .regexpReplaceAll("/index$", "")
}

/**
 * Gets a node believed to originate from `package`.
 *
 * The package is normalized by `normalizePackageName`.
 */
API::Node getANodeFromPackage(string package) {
  exists(string importString |
    result = API::moduleImport(importString) and
    package = normalizePackageName(importString)
  )
  or
  result = getANodeFromPackage(package).getAMember() and
  not result.asSource() = blockedNode()
  or
  result = getANodeFromPackage(package).getReturn()
  or
  result = getANodeFromPackage(package).getInstance()
  or
  result = getANodeFromPackage(package).getAParameter().getAParameter()
  or
  result = getANodeFromPackage(package).getAParameter().getAMember().getAParameter()
  or
  result = getANodeFromPackage(package).getPromised()
}

/**
 * Gets a call targeting targeting a method named `methodName` in `package`.
 */
DataFlow::InvokeNode getANamedExternalCall(string package, string methodName) {
  exists(API::Node member |
    member = getANodeFromPackage(package).getMember(methodName) and
    result = member.getAnInvocation() and
    not member.asSource() = blockedNode() and
    not (methodName = "default" and member.asSource() instanceof DataFlow::ModuleImportNode)
  )
}

/**
 * Gets a call that invokes `package` as a function (that is, its exported object is a function).
 */
DataFlow::InvokeNode getADirectExternalCall(string package) {
  result = API::moduleImport(package).getAnInvocation()
}

/**
 * Gets a call target likely targets `package`, but with no associated method name.
 *
 * For example:
 * ```javascript
 * const lib = require('example')
 *
 * let fn = lib();
 * fn() // curried calls are considered anonymous
 *
 * lib(fn => {
 *   fn(); // callback invocation is considered anonymous
 * })
 *
 * lib[complicated()](); // method call with unknown name
 * ```
 */
DataFlow::InvokeNode getAnAnonymousExternalCall(string package) {
  result = getANodeFromPackage(package).getAnInvocation() and
  not result = getANodeFromPackage(package).getMember(_).getAnInvocation() and
  not result = getADirectExternalCall(package)
}
