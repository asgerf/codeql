/**
 * Provides Ruby specific classes and predicates for defining flow summaries.
 */

private import javascript
private import DataFlowImplSpecific::Private
private import DataFlowImplSpecific::Public
private import DataFlowImplCommon
private import FlowSummaryImpl::Private as Private
private import FlowSummaryImpl::Public
private import FlowSummary as FlowSummary
// Expose AccessPathSyntax to Flow
import semmle.javascript.frameworks.data.internal.AccessPathSyntax as AccessPathSyntax

class SummarizedCallableBase = string;

DataFlowCallable inject(SummarizedCallable c) { result.asLibraryCallable() = c }

/** Gets the parameter position representing a callback itself, if any. */
ArgumentPosition callbackSelfParameterPosition() { result.isFunctionSelfReference() }

/** Gets the synthesized data-flow call for `receiver`. */
SummaryCall summaryDataFlowCall(Private::SummaryNode receiver) { receiver = result.getReceiver() }

/** Gets the type of content `c`. */
DataFlowType getContentType(ContentSet c) { any() }

/** Gets the type of the parameter at the given position. */
bindingset[c, pos]
DataFlowType getParameterType(SummarizedCallable c, ParameterPosition pos) { any() }

/** Gets the return type of kind `rk` for callable `c`. */
bindingset[c, rk]
DataFlowType getReturnType(SummarizedCallable c, ReturnKind rk) { any() }

/**
 * Gets the type of the `i`th parameter in a synthesized call that targets a
 * callback of type `t`.
 */
bindingset[t, pos]
DataFlowType getCallbackParameterType(DataFlowType t, ArgumentPosition pos) { any() }

/**
 * Gets the return type of kind `rk` in a synthesized call that targets a
 * callback of type `t`.
 */
DataFlowType getCallbackReturnType(DataFlowType t, ReturnKind rk) { any() }

/** Gets the type of synthetic global `sg`. */
DataFlowType getSyntheticGlobalType(SummaryComponent::SyntheticGlobal sg) { any() }

/**
 * Holds if an external flow summary exists for `c` with input specification
 * `input`, output specification `output`, kind `kind`, and provenance `provenance`.
 */
predicate summaryElement(
  FlowSummary::SummarizedCallable c, string input, string output, string kind, string provenance
) {
  exists(boolean preservesValue |
    c.propagatesFlowExt(input, output, preservesValue) and
    (if preservesValue = true then kind = "value" else kind = "taint") and
    provenance = "manual"
  )
}

/**
 * Holds if a neutral summary model exists for `c` with provenance `provenance`,
 * which means that there is no flow through `c`.
 * Note. Neutral models have not been implemented for Ruby.
 */
predicate neutralSummaryElement(FlowSummary::SummarizedCallable c, string provenance) { none() }

pragma[inline]
private SummaryComponent makeContentComponents(
  Private::AccessPathToken token, string name, ContentSet contents
) {
  token.getName() = name and
  result = FlowSummary::SummaryComponent::content(contents)
  or
  token.getName() = "With" + name and
  result = FlowSummary::SummaryComponent::withContent(contents)
  or
  token.getName() = "Without" + name and
  result = FlowSummary::SummaryComponent::withoutContent(contents)
}

pragma[inline]
private SummaryComponent makeSingletonContentComponents(
  Private::AccessPathToken token, string name, Content content
) {
  result = makeContentComponents(token, name, ContentSet::singleton(content))
}

pragma[inline]
private SummaryComponent makePropertyContentComponents(
  Private::AccessPathToken token, string name, PropertyName content
) {
  result = makeContentComponents(token, name, ContentSet::property(content))
}

/**
 * Gets the content corresponding to `Awaited[arg]`.
 */
private Content getPromiseContent(string arg) {
  arg = "value" and result.asPropertyName() = Promises::valueProp()
  or
  arg = "error" and result.asPropertyName() = Promises::errorProp()
}

pragma[nomagic]
private predicate positionName(ParameterPosition pos, string operand) {
  operand = pos.asPositional().toString()
  or
  pos.isThis() and operand = "this"
  or
  pos.isFunctionSelfReference() and operand = "function"
  or
  pos.isArgumentsArray() and operand = "arguments-array"
  or
  operand = pos.asPositionalLowerBound() + ".."
}

/**
 * Holds if `operand` desugars to the given `pos`. Only used for parsing.
 */
bindingset[operand]
private predicate desugaredPositionName(ParameterPosition pos, string operand) {
  operand = "any" and
  pos.asPositionalLowerBound() = 0
  or
  pos.asPositional() = AccessPathSyntax::AccessPath::parseInt(operand) // parse closed intervals
}

bindingset[operand]
private ParameterPosition parsePosition(string operand) {
  positionName(result, operand) or desugaredPositionName(result, operand)
}

/**
 * Gets the summary component for specification component `c`, if any.
 *
 * This covers all the Ruby-specific components of a flow summary.
 */
SummaryComponent interpretComponentSpecific(Private::AccessPathToken c) {
  c.getName() = "Argument" and
  result = FlowSummary::SummaryComponent::argument(parsePosition(c.getAnArgument()))
  or
  c.getName() = "Parameter" and
  result = FlowSummary::SummaryComponent::parameter(parsePosition(c.getAnArgument()))
  or
  result = makePropertyContentComponents(c, "Member", c.getAnArgument())
  or
  result =
    makePropertyContentComponents(c, "ArrayElement", DataFlow::PseudoProperties::arrayElement())
  or
  result = makePropertyContentComponents(c, "MapValue", DataFlow::PseudoProperties::mapValueAll())
  or
  result = makePropertyContentComponents(c, "PromiseValue", Promises::valueProp())
  or
  result = makeSingletonContentComponents(c, "Awaited", getPromiseContent(c.getAnArgument()))
  or
  // 'Awaited' is a special operator that we encode as content components, but it doesn't behave exactly that way.
  // It is mapped down to a combination steps that handle coercion and promise-flattening.
  c.getName() = "Awaited" and
  c.getNumArgument() = 0 and
  result = SummaryComponent::content(MkAwaited())
  or
  c.getName() = "ReturnValue" and
  c.getAnArgument() = "exception" and
  result = SummaryComponent::return(MkExceptionalReturnKind())
}

private string getMadStringFromContentSetAux(ContentSet cs) {
  cs.asPropertyName() = DataFlow::PseudoProperties::arrayElement() and result = "ArrayElement"
  or
  cs.asPropertyName() = DataFlow::PseudoProperties::mapValueAll() and result = "MapValue"
  or
  exists(string awaitedArg |
    cs.asSingleton() = getPromiseContent(awaitedArg) and
    result = "Awaited[" + awaitedArg + "]"
  )
  or
  cs = MkAwaited() and result = "Awaited"
}

private string getMadStringFromContentSet(ContentSet cs) {
  result = getMadStringFromContentSetAux(cs)
  or
  not exists(getMadStringFromContentSetAux(cs)) and
  result = "Member[" + cs.asSingleton() + "]"
}

/** Gets the textual representation of a summary component in the format used for MaD models. */
string getMadRepresentationSpecific(SummaryComponent sc) {
  exists(ContentSet cs |
    sc = Private::TContentSummaryComponent(cs) and result = getMadStringFromContentSet(cs)
  )
  or
  exists(ReturnKind rk |
    sc = Private::TReturnSummaryComponent(rk) and
    not rk = getReturnValueKind() and
    result = "ReturnValue[" + rk + "]"
  )
}

/** Gets the textual representation of a parameter position in the format used for flow summaries. */
bindingset[pos]
string getParameterPosition(ParameterPosition pos) { positionName(pos, result) and result != "any" }

/** Gets the textual representation of an argument position in the format used for flow summaries. */
bindingset[pos]
string getArgumentPosition(ArgumentPosition pos) { positionName(pos, result) and result != "any" }

/** Holds if input specification component `c` needs a reference. */
predicate inputNeedsReferenceSpecific(string c) { none() }

/** Holds if output specification component `c` needs a reference. */
predicate outputNeedsReferenceSpecific(string c) { none() }

/** Gets the return kind corresponding to specification `"ReturnValue"`. */
MkNormalReturnKind getReturnValueKind() { any() }

/**
 * All definitions in this module are required by the shared implementation
 * (for source/sink interpretation), but they are unused for JS, where
 * we rely on API graphs instead.
 */
private module UnusedSourceSinkInterpretation {
  /**
   * Holds if an external source specification exists for `n` with output specification
   * `output`, kind `kind`, and provenance `provenance`.
   */
  predicate sourceElement(AstNode n, string output, string kind, string provenance) { none() }

  /**
   * Holds if an external sink specification exists for `n` with input specification
   * `input`, kind `kind` and provenance `provenance`.
   */
  predicate sinkElement(AstNode n, string input, string kind, string provenance) { none() }

  class SourceOrSinkElement = AstNode;

  /** An entity used to interpret a source/sink specification. */
  class InterpretNode extends AstNode {
    /** Gets the element that this node corresponds to, if any. */
    SourceOrSinkElement asElement() { none() }

    /** Gets the data-flow node that this node corresponds to, if any. */
    Node asNode() { none() }

    /** Gets the call that this node corresponds to, if any. */
    DataFlowCall asCall() { none() }

    /** Gets the callable that this node corresponds to, if any. */
    DataFlowCallable asCallable() { none() }

    /** Gets the target of this call, if any. */
    StmtContainer getCallTarget() { none() }
  }

  /** Provides additional sink specification logic. */
  predicate interpretOutputSpecific(string c, InterpretNode mid, InterpretNode node) { none() }

  /** Provides additional source specification logic. */
  predicate interpretInputSpecific(string c, InterpretNode mid, InterpretNode node) { none() }
}

import UnusedSourceSinkInterpretation

/** Gets the argument position obtained by parsing `X` in `Parameter[X]`. */
bindingset[s]
ArgumentPosition parseParamBody(string s) {
  s = "this" and result.isThis()
  or
  s = "function" and result.isFunctionSelfReference()
  or
  result.asPositional() = AccessPathSyntax::AccessPath::parseInt(s)
}

/** Gets the parameter position obtained by parsing `X` in `Argument[X]`. */
bindingset[s]
ParameterPosition parseArgBody(string s) {
  result = parseParamBody(s) // Currently these are identical
}
