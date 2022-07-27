/**
 * Provides classes for working with applications using [snapdragon](https://www.npmjs.com/package/snapdragon).
 */

import javascript

/**
 * A module modeling taint steps for the [snapdragon](https://www.npmjs.com/package/snapdragon) library.
 */
private module Snapdragon {
  private class SnapdragonInstance extends API::Node {
    SnapdragonInstance() { this = API::moduleImport("snapdragon").getInstance() }

    API::Node ref() { result = this or result = this.ref().getMember("set").getReturn() }

    API::Node getComponent(string kind) {
      kind = ["parse", "compile"] and
      result = this.ref().getMember(kind + "r")
      or
      result = this.getComponent(kind).getMember("set").getReturn()
    }

    DataFlow::Node getInput(string kind) {
      kind = ["parse", "compile"] and
      result = this.ref().getMember(kind).getParameter(0).asSink()
    }

    DataFlow::SourceNode getOutput(string kind) {
      kind = "parse" and
      result = this.getComponent("parse").getMember("set").getParameter(1).getReceiver()
      or
      kind = "compile" and
      result = this.getComponent("compile").getMember("set").getParameter(1).getParameter(0)
    }
  }

  /**
   * A taint step through the [snapdragon](https://www.npmjs.com/package/snapdragon) library.
   *
   * Models both parsing (converting a string to an AST) and compilation (converting an AST to a string).
   * For example:
   * ```JavaScript
   * var snapdragon = new (require("snapdragon"))();
   * snapdragon.parser.set("foo", function () {
   *  sink(this); // <- sink
   * });
   * snapdragon.parse("source", opts); // <- source
   * ```
   */
  private class SnapDragonStep extends DataFlow::SharedFlowStep {
    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      exists(SnapdragonInstance inst, string kind |
        pred = inst.getInput(kind) and
        succ = inst.getOutput(kind)
      )
    }
  }
}
