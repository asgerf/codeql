/**
 * Provides default sources for reasoning about DOM-based
 * cross-site scripting vulnerabilities.
 */

import javascript

module DomBasedXss {
  import Xss::DomBasedXss

  /** A source of remote user input, considered as a flow source for DOM-based XSS. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * Holds if the DomBasedXSS query should propagate taint along the edge `pred -> succ`.
   */
  predicate isRequestForgeryStep(DataFlow::Node pred, DataFlow::Node succ) {
    // On the client side, we don't warn about request forgery on its own.
    // Instead we use this step to check if it can escalate to XSS.
    exists(ClientRequest req |
      pred = [req.getUrl(), req.getHost()] and
      succ = req.getAResponseDataNode()
    )
  }
}
