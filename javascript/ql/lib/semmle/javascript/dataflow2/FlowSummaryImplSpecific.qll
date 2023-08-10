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
ArgumentPosition callbackSelfParameterPosition() { none() } // disables implicit summary flow to `self` for callbacks

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
private SummaryComponent makeContentComponts(
  Private::AccessPathToken token, string name, string content
) {
  token.getName() = name and
  result = FlowSummary::SummaryComponent::content(content)
  or
  token.getName() = "With" + name and
  result = FlowSummary::SummaryComponent::withContent(content)
  or
  token.getName() = "Without" + name and
  result = FlowSummary::SummaryComponent::withoutContent(content)
}

/**
 * Gets the summary component for specification component `c`, if any.
 *
 * This covers all the Ruby-specific components of a flow summary.
 */
SummaryComponent interpretComponentSpecific(Private::AccessPathToken c) {
  exists(string arg, ParameterPosition ppos |
    c.getName() = "Argument" and
    arg = c.getAnArgument() and
    result = FlowSummary::SummaryComponent::argument(ppos)
  |
    // TODO: convert ParameterPosition to a newtype and then update this
    arg = "any" and
    ppos = [0 .. 10]
    or
    ppos = [AccessPathSyntax::AccessPath::parseLowerBound(arg) .. 10]
  )
  or
  result = makeContentComponts(c, "Member", c.getAnArgument())
  or
  result = makeContentComponts(c, "ArrayElement", DataFlow::PseudoProperties::arrayElement())
  or
  result = makeContentComponts(c, "MapValue", DataFlow::PseudoProperties::mapValueAll())
  or
  result = makeContentComponts(c, "Awaited", Promises::valueProp())
  or
  result = makeContentComponts(c, "AwaitedError", Promises::errorProp())
}

private string getContentSpecificAux(Content c) {
  c = DataFlow::PseudoProperties::arrayElement() and result = "ArrayElement"
  or
  c = DataFlow::PseudoProperties::mapValueAll() and result = "MapValue"
  or
  c = Promises::valueProp() and result = "Awaited"
  or
  c = Promises::errorProp() and result = "AwaitedError"
}

private string getContentSpecific(Content c) {
  result = getContentSpecificAux(c)
  or
  not exists(getContentSpecificAux(c)) and
  result = "Member[" + c + "]"
}

private string getContentSetSpecific(ContentSet cs) { result = getContentSpecific(cs) }

/** Gets the textual representation of a summary component in the format used for MaD models. */
string getMadRepresentationSpecific(SummaryComponent sc) {
  exists(ContentSet cs |
    sc = Private::TContentSummaryComponent(cs) and result = getContentSetSpecific(cs)
  )
  or
  exists(ContentSet cs |
    sc = Private::TWithoutContentSummaryComponent(cs) and
    result = "WithoutElement[" + getContentSetSpecific(cs) + "]"
  )
  or
  exists(ContentSet cs |
    sc = Private::TWithContentSummaryComponent(cs) and
    result = "WithElement[" + getContentSetSpecific(cs) + "]"
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
string getParameterPosition(ParameterPosition pos) {
  pos >= 0 and result = pos.toString()
  or
  pos = -1 and result = "this"
}

/** Gets the textual representation of an argument position in the format used for flow summaries. */
bindingset[pos]
string getArgumentPosition(ArgumentPosition pos) {
  pos >= 0 and result = pos.toString()
  or
  pos = -1 and result = "this"
}

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
  s = "this" and result = -1
  or
  result = AccessPathSyntax::AccessPath::parseInt(s) and result >= 0
}

/** Gets the parameter position obtained by parsing `X` in `Argument[X]`. */
bindingset[s]
ParameterPosition parseArgBody(string s) {
  result = parseParamBody(s) // Currently these are identical
}
