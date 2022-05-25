private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "pg-cursor;Static;Argument[0];sql-injection", //
        "pg;ClientBase;Member[query].Argument[0];sql-injection", //
        "pg;ClientConfig;Member[password];credentials[password]", //
        "pg;ClientConfig;Member[user];credentials[username]", //
        "pg;Connection;Member[execute,query].Argument[0];sql-injection", //
        "pg;Pool;Member[query].Argument[0];sql-injection", //
        "pg;QueryConfig;Member[text];sql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "pg-cursor;;pg-cursor;Static;Instance", //
        "pg-cursor;Static;pg-cursor;;", //
        "pg-pool;;pg-pool;Static;Instance", //
        "pg-pool;ClientLikeCtr;pg-pool;;Member[Client]", //
        "pg-pool;ClientLikeCtr;pg-pool;Config;Member[Client]", //
        "pg-pool;ClientLikeCtr;pg-pool;Static;Argument[1]", //
        "pg-pool;Config;pg-pool;Static;Argument[0]", //
        "pg-pool;Static;pg-pool;;", //
        "pg;Client;pg;ClientStatic;Instance", //
        "pg;Client;pg;Events;Member[on].Argument[1].Argument[1]", //
        "pg;ClientBase;pg;Client;", //
        "pg;ClientBase;pg;ClientBaseStatic;Instance", //
        "pg;ClientBase;pg;PoolClient;", //
        "pg;ClientBaseStatic;pg;;Member[ClientBase]", //
        "pg;ClientConfig;pg-pool;ClientLikeCtr;Argument[0]", //
        "pg;ClientConfig;pg;;Member[defaults]", //
        "pg;ClientConfig;pg;ClientBaseStatic;Argument[0]", //
        "pg;ClientConfig;pg;ClientStatic;Argument[0]", //
        "pg;ClientConfig;pg;ConnectionConfig;", //
        "pg;ClientConfig;pg;Defaults;", //
        "pg;ClientConfig;pg;PoolConfig;", //
        "pg;ClientStatic;pg;;Member[Client]", //
        "pg;Connection;pg-cursor;;Member[submit].Argument[0]", //
        "pg;Connection;pg;ConnectionStatic;Instance", //
        "pg;Connection;pg;Query;Member[submit].Argument[0]", //
        "pg;Connection;pg;Submittable;Member[submit].Argument[0]", //
        "pg;ConnectionConfig;pg;ConnectionStatic;Argument[0]", //
        "pg;ConnectionStatic;pg;;Member[Connection]", //
        "pg;Defaults;pg;;Member[defaults]", //
        "pg;Events;pg;EventsStatic;Instance", //
        "pg;EventsStatic;pg;;Member[Events]", //
        "pg;Pool;pg-pool;;", //
        "pg;Pool;pg;PoolStatic;Instance", //
        "pg;PoolClient;pg-pool;;Member[connect].Argument[0].Argument[1]", //
        "pg;PoolClient;pg-pool;;Member[connect].ReturnValue.Awaited", //
        "pg;PoolClient;pg-pool;;Member[on].Argument[1].Argument[0,1]", //
        "pg;PoolClient;pg;Pool;Member[connect].Argument[0].Argument[1]", //
        "pg;PoolClient;pg;Pool;Member[connect].ReturnValue.Awaited", //
        "pg;PoolClient;pg;Pool;Member[on].Argument[1].Argument[0,1]", //
        "pg;PoolConfig;pg-pool;Config;", //
        "pg;PoolConfig;pg;PoolStatic;Argument[0]", //
        "pg;PoolStatic;pg;;Member[Pool]", //
        "pg;Query;pg;QueryStatic;Instance", //
        "pg;QueryArrayConfig;pg;ClientBase;Member[query].Argument[0]", //
        "pg;QueryArrayConfig;pg;Pool;Member[query].Argument[0]", //
        "pg;QueryConfig;pg;ClientBase;Member[query].Argument[0]", //
        "pg;QueryConfig;pg;Pool;Member[query].Argument[0]", //
        "pg;QueryConfig;pg;QueryArrayConfig;", //
        "pg;QueryConfig;pg;QueryStatic;Argument[0]", //
        "pg;QueryStatic;pg;;Member[Query]", //
        "pg;Submittable;pg;Query;", //
      ]
  }
}
