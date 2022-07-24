const cp = require('child_process');

module.exports = function () {
    return cp.spawn.bind(
        cp,   // def=moduleImport("child_process").getMember("spawn").getReceiver()
        "cat" // def=moduleImport("child_process").getMember("spawn").getParameter(0)
    );
};
