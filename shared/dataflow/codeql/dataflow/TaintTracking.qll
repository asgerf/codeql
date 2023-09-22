/**
 * Provides modules for performing local (intra-procedural) and
 * global (inter-procedural) taint-tracking analyses.
 */

private import DataFlow as DF
private import internal.DataFlowImpl

/**
 * Provides language-specific taint-tracking parameters.
 */
signature module InputSig<DF::InputSig Lang> {
  /**
   * Holds if `node` should be a sanitizer in all global taint flow configurations
   * but not in local taint.
   */
  predicate defaultTaintSanitizer(Lang::Node node);

  /**
   * Holds if the additional step from `src` to `sink` should be included in all
   * global taint flow configurations.
   */
  predicate defaultAdditionalTaintStep(Lang::Node src, Lang::Node sink);

  /**
   * Holds if taint flow configurations should allow implicit reads of `c` at sinks
   * and inputs to additional taint steps.
   */
  bindingset[node]
  predicate defaultImplicitTaintRead(Lang::Node node, Lang::ContentSet c);
}

/**
 * Construct the modules for taint-tracking analyses.
 */
module TaintFlowMake<DF::InputSig DataFlowLang, InputSig<DataFlowLang> TaintTrackingLang> {
  private import TaintTrackingLang
  private import DF::DataFlowMake<DataFlowLang> as DataFlow
  private import MakeImpl<DataFlowLang> as DataFlowInternal

  private module AddTaintDefaults<DataFlowInternal::FullStateConfigSig Config> implements
    DataFlowInternal::FullStateConfigSig
  {
    import Config

    private predicate isFlowState(Config::FlowState state) {
      Config::isAdditionalFlowStep(_, state, _, _) or
      Config::isAdditionalFlowStep(_, _, _, state) or
      Config::isSink(_, state) or
      Config::isSource(_, state)
    }

    private predicate isTaintFlowState(FlowState state) {
      isFlowState(state) and
      not Config::isValueOnlyFlowState(state)
    }

    predicate isBarrier(DataFlowLang::Node node, FlowState state) {
      Config::isBarrier(node, state)
      or
      isTaintFlowState(state) and
      defaultTaintSanitizer(node)
    }

    predicate isAdditionalFlowStep(
      DataFlowLang::Node node1, Config::FlowState state1, DataFlowLang::Node node2,
      Config::FlowState state2
    ) {
      Config::isAdditionalFlowStep(node1, state1, node2, state2)
      or
      defaultAdditionalTaintStep(node1, node2) and
      isTaintFlowState(state1) and
      state2 = state1
    }

    predicate allowImplicitRead(DataFlowLang::Node node, DataFlowLang::ContentSet c) {
      Config::allowImplicitRead(node, c)
      or
      (
        Config::isSink(node)
        or
        Config::isAdditionalFlowStep(node, _)
        or
        exists(Config::FlowState state | not Config::isValueOnlyFlowState(state) |
          // Flow state-specific implicit reads are not supported, so as a best approximation,
          // include them at sinks and additional steps for any taint flow state, even though other flow states can use them.
          Config::isSink(node, state) or
          Config::isAdditionalFlowStep(node, state, _, _)
        )
      ) and
      defaultImplicitTaintRead(node, c)
    }
  }

  /**
   * Constructs a global taint tracking computation.
   */
  module Global<DataFlow::ConfigSig Config> implements DataFlow::GlobalFlowSig {
    private module Config0 implements DataFlowInternal::FullStateConfigSig {
      import DataFlowInternal::DefaultState<Config>
      import Config
    }

    private module C implements DataFlowInternal::FullStateConfigSig {
      import AddTaintDefaults<Config0>
    }

    import DataFlowInternal::Impl<C>
  }

  /** DEPRECATED: Use `Global` instead. */
  deprecated module Make<DataFlow::ConfigSig Config> implements DataFlow::GlobalFlowSig {
    import Global<Config>
  }

  /**
   * Constructs a global taint tracking computation using flow state.
   */
  module GlobalWithState<DataFlow::StateConfigSig Config> implements DataFlow::GlobalFlowSig {
    private module Config0 implements DataFlowInternal::FullStateConfigSig {
      import Config
    }

    private module C implements DataFlowInternal::FullStateConfigSig {
      import AddTaintDefaults<Config0>
    }

    import DataFlowInternal::Impl<C>
  }

  /** DEPRECATED: Use `GlobalWithState` instead. */
  deprecated module MakeWithState<DataFlow::StateConfigSig Config> implements
    DataFlow::GlobalFlowSig
  {
    import GlobalWithState<Config>
  }
}
