import javascript

query predicate flowSteps(DataFlow::Node pred, DataFlow::Node succ) {
  DataFlow::SharedFlowStep::step(pred, succ) and
  not pred instanceof DataFlow::PostUpdateNode
}

query predicate eventEmitter(EventEmitter e) { any() }
