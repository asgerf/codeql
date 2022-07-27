/** Provides classes and predicates modeling aspects of the [`history`](https://npmjs.org/package/history) library. */

import javascript

/** Provides classes modeling the [`history`](https://npmjs.org/package/history) library. */
module History {
  /**
   * Gets a reference to the [`history`](https://npmjs.org/package/history) library.
   */
  private API::Node history() {
    result = API::moduleImport("history")
    or
    result = DataFlow::globalVarRef("HistoryLibrary")
  }

  /**
   * Gets a browser history instance.
   * This history instance uses the native browser history API.
   */
  API::Node getBrowserHistory() { result = history().getMember("createBrowserHistory").getReturn() }

  /**
   * Gets a hash history instance.
   * This history instance only manipulates the URL hash, which cannot cause XSS.
   */
  API::Node getHashHistory() { result = history().getMember("createHashHistory").getReturn() }

  /**
   * A user-controlled location value read from the [history](http://npmjs.org/package/history) library.
   */
  private class HistoryLibraryRemoteFlow extends ClientSideRemoteFlowSource {
    ClientSideRemoteFlowKind kind;

    HistoryLibraryRemoteFlow() {
      exists(API::Node loc | loc = [getBrowserHistory(), getHashHistory()].getMember("location") |
        this = loc.getMember("hash").asSource() and kind.isFragment()
        or
        this = loc.getMember("pathname").asSource() and kind.isPath()
        or
        this = loc.getMember("search").asSource() and kind.isQuery()
      )
    }

    override string getSourceType() { result = "Window location" }

    override ClientSideRemoteFlowKind getKind() { result = kind }
  }
}
