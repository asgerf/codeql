private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "mysql;;Member[raw].Argument[0];sql-injection", //
        "mysql;QueryFunction;Argument[0];sql-injection", //
        "mysql;QueryOptions;Member[sql];sql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "mysql;Connection;mysql;;Member[createConnection].ReturnValue", //
        "mysql;Connection;mysql;PoolConnection;", //
        "mysql;Connection;mysql;Query;Member[RowDataPacket].Argument[2]", //
        "mysql;Pool;mysql;;Member[createPool].ReturnValue", //
        "mysql;Pool;mysql;PoolCluster;Member[of].ReturnValue", //
        "mysql;PoolCluster;mysql;;Member[createPoolCluster].ReturnValue", //
        "mysql;PoolConnection;mysql;Pool;Member[acquireConnection].Argument[0]", //
        "mysql;PoolConnection;mysql;Pool;Member[acquireConnection].Argument[1].Argument[1]", //
        "mysql;PoolConnection;mysql;Pool;Member[getConnection].Argument[0].Argument[1]", //
        "mysql;PoolConnection;mysql;PoolCluster;Member[getConnection].Argument[0,1,2].Argument[1]", //
        "mysql;Query;mysql;Query;Member[on].ReturnValue", //
        "mysql;Query;mysql;QueryFunction;Argument[0]", //
        "mysql;Query;mysql;QueryFunction;ReturnValue", //
        "mysql;QueryFunction;mysql;Connection;Member[createQuery,query]", //
        "mysql;QueryFunction;mysql;Pool;Member[query]", //
        "mysql;QueryOptions;mysql;Connection;Member[beginTransaction,commit,ping,rollback,statistics].Argument[0]", //
        "mysql;QueryOptions;mysql;QueryFunction;Argument[0]", //
      ]
  }
}
