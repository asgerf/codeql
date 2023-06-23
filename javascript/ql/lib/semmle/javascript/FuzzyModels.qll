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

bindingset[rawPackage]
private string normalizePackageName(string rawPackage) {
  result = rawPackage.regexpReplaceAll("^node:", "")
}

API::Node getANodeFromPackage(string package) {
  exists(string rawPackage |
    result = API::moduleImport(rawPackage) and
    package = normalizePackageName(rawPackage)
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

DataFlow::InvokeNode namedExternalCallLike(string package, string methodName) {
  result = getANodeFromPackage(package).getMember(methodName).getAnInvocation()
}

DataFlow::InvokeNode namedExternalCall(string package, string methodName) {
  exists(API::Node member |
    member = getANodeFromPackage(package).getMember(methodName) and
    result = member.getAnInvocation() and
    not member.asSource() = blockedNode() and
    not (methodName = "default" and member.asSource() instanceof DataFlow::ModuleImportNode)
  )
}

DataFlow::InvokeNode directExternalCall(string package) {
  result = API::moduleImport(package).getAnInvocation()
}

DataFlow::InvokeNode anonymousExternalCall(string package) {
  result = getANodeFromPackage(package).getAnInvocation() and
  not result = namedExternalCallLike(package, _) and
  not result = directExternalCall(package)
}

DataFlow::InvokeNode externalCall(string package, string methodName) {
  result = namedExternalCall(package, methodName)
  or
  methodName = "(direct call)" and
  result = directExternalCall(package)
  or
  methodName = "(anonymous call)" and
  result = anonymousExternalCall(package)
}
