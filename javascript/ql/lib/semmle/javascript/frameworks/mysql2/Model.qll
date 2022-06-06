private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "mysql2/promise;Connection;Member[execute].Argument[0];sql-injection", //
        "mysql2/promise;Pool;Member[execute].Argument[0];sql-injection", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;Member[sql];sql-injection", //
        "mysql2;Connection;Member[execute].Argument[0];sql-injection", //
        "mysql2;Pool;Member[execute].Argument[0];sql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "mysql2/promise;Connection;mysql2/promise;;Member[createConnection].ReturnValue.Awaited", //
        "mysql2/promise;Connection;mysql2/promise;PoolConnection;", //
        "mysql2/promise;Connection;mysql2;Connection;Member[promise].ReturnValue", //
        "mysql2/promise;Pool;mysql2/promise;;Member[createPool].ReturnValue", //
        "mysql2/promise;Pool;mysql2;Pool;Member[promise].ReturnValue", //
        "mysql2/promise;PoolConnection;mysql2/promise;Pool;Member[getConnection].ReturnValue.Awaited", //
        "mysql2/promise;PoolConnection;mysql2/promise;Pool;Member[on].Argument[1].Argument[0]", //
        "mysql2/promise;PoolConnection;mysql2;PoolConnection;Member[promise].ReturnValue", //
        "mysql2/typings/mysql/lib/Connection;;mysql2/typings/mysql/lib/Connection;Static;ReturnValue", //
        "mysql2/typings/mysql/lib/Connection;;mysql2/typings/mysql/lib/PoolConnection;;", //
        "mysql2/typings/mysql/lib/Connection;;mysql2/typings/mysql;Connection;", //
        "mysql2/typings/mysql/lib/Connection;Static;mysql2/typings/mysql/lib/Connection;;", //
        "mysql2/typings/mysql/lib/Pool;;mysql2/typings/mysql/lib/Pool;Static;ReturnValue", //
        "mysql2/typings/mysql/lib/Pool;;mysql2/typings/mysql;Pool;", //
        "mysql2/typings/mysql/lib/Pool;Static;mysql2/typings/mysql/lib/Pool;;", //
        "mysql2/typings/mysql/lib/PoolCluster;;mysql2/typings/mysql/lib/PoolCluster;;Member[of].ReturnValue", //
        "mysql2/typings/mysql/lib/PoolCluster;;mysql2/typings/mysql/lib/PoolCluster;Static;ReturnValue", //
        "mysql2/typings/mysql/lib/PoolCluster;;mysql2;PoolCluster;", //
        "mysql2/typings/mysql/lib/PoolCluster;Static;mysql2/typings/mysql/lib/PoolCluster;;", //
        "mysql2/typings/mysql/lib/PoolConnection;;mysql2/typings/mysql/lib/Pool;;Member[getConnection].Argument[0].Argument[1]", //
        "mysql2/typings/mysql/lib/PoolConnection;;mysql2/typings/mysql/lib/Pool;;Member[on].Argument[1].Argument[0]", //
        "mysql2/typings/mysql/lib/PoolConnection;;mysql2/typings/mysql/lib/PoolCluster;;Member[getConnection].Argument[0,1,2].Argument[1]", //
        "mysql2/typings/mysql/lib/PoolConnection;;mysql2/typings/mysql/lib/PoolCluster;;Member[on].Argument[1].Argument[0]", //
        "mysql2/typings/mysql/lib/PoolConnection;;mysql2/typings/mysql/lib/PoolConnection;Static;ReturnValue", //
        "mysql2/typings/mysql/lib/PoolConnection;;mysql2/typings/mysql;PoolConnection;", //
        "mysql2/typings/mysql/lib/PoolConnection;Static;mysql2/typings/mysql/lib/PoolConnection;;", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;mysql2/promise;Connection;Member[execute,query].Argument[0]", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;mysql2/promise;Pool;Member[execute,query].Argument[0]", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;mysql2/typings/mysql/lib/Connection;;Member[query].Argument[0]", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;mysql2/typings/mysql/lib/Pool;;Member[query].Argument[0]", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;mysql2;Connection;Member[execute].Argument[0]", //
        "mysql2/typings/mysql/lib/protocol/sequences/Query;QueryOptions;mysql2;Pool;Member[execute].Argument[0]", //
        "mysql2/typings/mysql;Connection;mysql2/typings/mysql;;Member[createConnection].ReturnValue", //
        "mysql2/typings/mysql;Connection;mysql2;Connection;", //
        "mysql2/typings/mysql;Connection;mysql2;Pool;", //
        "mysql2/typings/mysql;Pool;mysql2/typings/mysql;;Member[createPool].ReturnValue", //
        "mysql2/typings/mysql;PoolConnection;mysql2;PoolConnection;", //
        "mysql2;Connection;mysql2;;Member[createConnection].ReturnValue", //
        "mysql2;Connection;mysql2;PoolConnection;", //
        "mysql2;Connection;mysql2;authPlugins;Argument[0].Member[connection]", //
        "mysql2;Pool;mysql2;;Member[createPool].ReturnValue", //
        "mysql2;PoolCluster;mysql2/promise;;Member[createPoolCluster].ReturnValue", //
        "mysql2;PoolCluster;mysql2/typings/mysql;;Member[createPoolCluster].ReturnValue", //
        "mysql2;PoolCluster;mysql2/typings/mysql;PoolCluster;", //
        "mysql2;PoolCluster;mysql2;;Member[createPoolCluster].ReturnValue", //
        "mysql2;PoolConnection;mysql2;Pool;Member[getConnection].Argument[0].Argument[1]", //
        "mysql2;PoolConnection;mysql2;Pool;Member[on].Argument[1].Argument[0]", //
      ]
  }
}
