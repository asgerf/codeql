private import javascript

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "pg-cursor;;pg-cursor;;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg-cursor;;pg-cursor;Static;Instance", //
        "pg-cursor;Static;pg-cursor;;", //
        "pg-pool;;pg-pool;;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg-pool;;pg-pool;Static;Instance", //
        "pg-pool;Static;pg-pool;;", //
        "pg;Client;pg;Client;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg;Client;pg;ClientStatic;Instance", //
        "pg;Client;pg;Events;Member[on].Argument[1].Argument[1]", //
        "pg;ClientStatic;pg;;Member[Client]", //
        "pg;Connection;pg-cursor;;Member[submit].Argument[0]", //
        "pg;Connection;pg;Connection;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg;Connection;pg;ConnectionStatic;Instance", //
        "pg;Connection;pg;Query;Member[submit].Argument[0]", //
        "pg;Connection;pg;Submittable;Member[submit].Argument[0]", //
        "pg;ConnectionStatic;pg;;Member[Connection]", //
        "pg;Events;pg;Events;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg;Events;pg;EventsStatic;Instance", //
        "pg;EventsStatic;pg;;Member[Events]", //
        "pg;Pool;pg-pool;;", //
        "pg;Pool;pg;Pool;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg;Pool;pg;PoolStatic;Instance", //
        "pg;PoolClient;pg-pool;;Member[connect].Argument[0].Argument[1]", //
        "pg;PoolClient;pg-pool;;Member[connect].WithArity[0].ReturnValue.Awaited", //
        "pg;PoolClient;pg-pool;;Member[on].WithArity[2].WithStringArgument[0=acquire,0=connect,0=remove].Argument[1].Argument[0]", //
        "pg;PoolClient;pg-pool;;Member[on].WithArity[2].WithStringArgument[0=error].Argument[1].Argument[1]", //
        "pg;PoolClient;pg;Pool;Member[connect].Argument[0].Argument[1]", //
        "pg;PoolClient;pg;Pool;Member[connect].WithArity[0].ReturnValue.Awaited", //
        "pg;PoolClient;pg;Pool;Member[on].WithArity[2].WithStringArgument[0=acquire,0=connect,0=remove].Argument[1].Argument[0]", //
        "pg;PoolClient;pg;Pool;Member[on].WithArity[2].WithStringArgument[0=error].Argument[1].Argument[1]", //
        "pg;PoolClient;pg;PoolClient;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg;PoolStatic;pg;;Member[Pool]", //
        "pg;Query;pg;Query;Member[addListener,off,on,once,prependListener,prependOnceListener,removeAllListeners,removeListener,setMaxListeners].ReturnValue", //
        "pg;Query;pg;QueryStatic;Instance", //
        "pg;QueryStatic;pg;;Member[Query]", //
        "pg;Submittable;pg;Query;", //
      ]
  }
}
