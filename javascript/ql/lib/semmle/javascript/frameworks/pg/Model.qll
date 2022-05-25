private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "pg;ClientBase;Member[query].Argument[0];sql-injection", //
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
        "pg;;pg;;", //
        "pg;Client;pg;ClientStatic;ReturnValue", //
        "pg;Client;pg;Events;Member[on].Argument[1].Argument[1]", //
        "pg;ClientBase;pg;Client;", //
        "pg;ClientBase;pg;ClientBaseStatic;ReturnValue", //
        "pg;ClientBase;pg;PoolClient;", //
        "pg;ClientBaseStatic;pg;;Member[ClientBase]", //
        "pg;ClientStatic;pg;;Member[Client]", //
        "pg;Connection;pg;ConnectionStatic;ReturnValue", //
        "pg;Connection;pg;Query;Member[submit].Argument[0]", //
        "pg;Connection;pg;Submittable;Member[submit].Argument[0]", //
        "pg;ConnectionStatic;pg;;Member[Connection]", //
        "pg;Events;pg;EventsStatic;ReturnValue", //
        "pg;EventsStatic;pg;;Member[Events]", //
        "pg;Pool;pg;PoolStatic;ReturnValue", //
        "pg;PoolClient;pg;Pool;Member[connect].Argument[0].Argument[1]", //
        "pg;PoolClient;pg;Pool;Member[connect].ReturnValue.Awaited", //
        "pg;PoolClient;pg;Pool;Member[on].Argument[1].Argument[0,1]", //
        "pg;PoolStatic;pg;;Member[Pool]", //
        "pg;Query;pg;QueryStatic;ReturnValue", //
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
