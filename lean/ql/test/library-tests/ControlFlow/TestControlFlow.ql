import javascript

class Source extends CallExpression {
  Source() { this.getFunction().(Identifier).getValue() = "source" }

  string getTag() { result = getStringValueFromNode(this.getArguments().(Arguments).getChild(0)) }
}

Source getSource(string tag) { result.getTag() = tag }

class Sink extends CallExpression {
  Sink() { this.getFunction().(Identifier).getValue() = "sink" }
}

boolean getDominatingOutcome(Sink sink, string tag) {
  exists(Source source | tag = source.getTag() |
    Cfg::dominates(getTrueOutcomeNode(source), sink) and result = true
    or
    Cfg::dominates(getFalseOutcomeNode(source), sink) and result = false
  )
}

predicate isDominatingNoOutcome(Sink sink, string tag) {
  not exists(getDominatingOutcome(sink, tag)) and
  Cfg::dominates(getSource(tag), sink)
}

string getDominatingOutcomeExpectation(Sink sink, string tag) {
  result = tag + "-" + getDominatingOutcome(sink, tag)
  or
  isDominatingNoOutcome(sink, tag) and
  result = tag
}

query predicate dominatedBy(Sink sink, string value) {
  value = getDominatingOutcomeExpectation(sink, _)
}

private boolean getAReachingOutcome(Sink sink, string tag) {
  exists(Source source | tag = source.getTag() |
    Cfg::step+(getTrueOutcomeNode(source), sink) and result = true
    or
    Cfg::step+(getFalseOutcomeNode(source), sink) and result = false
    or
    not isCondition(source) and
    Cfg::step+(source, sink) and
    result = [true, false]
  )
}

private boolean getUniqueReachingOutcome(Sink sink, string tag) {
  result = unique( | | getAReachingOutcome(sink, tag))
}

string getReachingOutcomeExpectation(Sink sink, string tag) {
  result = tag + "-" + getUniqueReachingOutcome(sink, tag)
  or
  exists(getAReachingOutcome(sink, tag)) and
  not exists(getUniqueReachingOutcome(sink, tag)) and
  result = tag
}

query predicate reachedBy(Sink sink, string value) {
  exists(string tag |
    not exists(getDominatingOutcomeExpectation(sink, tag)) and
    value = getReachingOutcomeExpectation(sink, tag)
  )
}

query predicate unreachable(Sink sink) { not Cfg::step+(getCfgEntryPoint(getCfgScope(sink)), sink) }

query predicate tagIsNotUnique(Source source, string tag) {
  tag = source.getTag() and
  strictcount(getSource(tag)) > 1
}
