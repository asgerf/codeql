private import javascript

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "@google-cloud/spanner/batch-transaction;BatchTransaction;@google-cloud/spanner/batch-transaction;BatchTransactionStatic;Instance", //
        "@google-cloud/spanner/batch-transaction;BatchTransaction;@google-cloud/spanner/database;CreateBatchTransactionCallback;Argument[1]", //
        "@google-cloud/spanner/batch-transaction;BatchTransaction;@google-cloud/spanner;Database;Member[batchTransaction].ReturnValue", //
        "@google-cloud/spanner/batch-transaction;BatchTransactionStatic;@google-cloud/spanner/batch-transaction;;Member[BatchTransaction]", //
        "@google-cloud/spanner/database;CreateBatchTransactionCallback;@google-cloud/spanner;Database;Member[createBatchTransaction].Argument[1]", //
        "@google-cloud/spanner/database;CreateBatchTransactionCallback;@google-cloud/spanner;Database;Member[createBatchTransaction].WithArity[1].Argument[0]", //
        "@google-cloud/spanner/database;DatabaseCallback;@google-cloud/spanner;Database;Member[get].Argument[1]", //
        "@google-cloud/spanner/database;DatabaseCallback;@google-cloud/spanner;Database;Member[get].WithArity[1].Argument[0]", //
        "@google-cloud/spanner/database;RestoreDatabaseCallback;@google-cloud/spanner;Database;Member[restore].Argument[1,2]", //
        "@google-cloud/spanner/database;SessionPoolConstructor;@google-cloud/spanner;DatabaseStatic;Argument[2]", //
        "@google-cloud/spanner/database;SessionPoolConstructor;@google-cloud/spanner;Instance;Member[database].Argument[1]", //
        "@google-cloud/spanner/instance;CreateDatabaseCallback;@google-cloud/spanner;Instance;Member[createDatabase].Argument[2]", //
        "@google-cloud/spanner/instance;CreateDatabaseCallback;@google-cloud/spanner;Instance;Member[createDatabase].WithArity[2].Argument[1]", //
        "@google-cloud/spanner/instance;CreateDatabaseOptions;@google-cloud/spanner;Instance;Member[createDatabase].WithArity[1..2,3].Argument[1]", //
        "@google-cloud/spanner/instance;CreateInstanceCallback;@google-cloud/spanner;Spanner;Member[createInstance].Argument[2]", //
        "@google-cloud/spanner/instance;GetDatabasesCallback;@google-cloud/spanner;Instance;Member[getDatabases].Argument[1]", //
        "@google-cloud/spanner/instance;GetDatabasesCallback;@google-cloud/spanner;Instance;Member[getDatabases].WithArity[1].Argument[0]", //
        "@google-cloud/spanner/instance;GetDatabasesResponse;@google-cloud/spanner;Instance;Member[getDatabases].WithArity[0..1].ReturnValue.Awaited", //
        "@google-cloud/spanner/instance;GetInstanceCallback;@google-cloud/spanner;Instance;Member[get].Argument[1]", //
        "@google-cloud/spanner/instance;GetInstanceCallback;@google-cloud/spanner;Instance;Member[get].WithArity[1].Argument[0]", //
        "@google-cloud/spanner/table;CreateTableCallback;@google-cloud/spanner;Database;Member[createTable].Argument[2]", //
        "@google-cloud/spanner/table;CreateTableCallback;@google-cloud/spanner;Database;Member[createTable].WithArity[2].Argument[1]", //
        "@google-cloud/spanner/table;CreateTableCallback;@google-cloud/spanner;Table;Member[create].Argument[2]", //
        "@google-cloud/spanner/table;CreateTableCallback;@google-cloud/spanner;Table;Member[create].WithArity[2].Argument[1]", //
        "@google-cloud/spanner;BackupStatic;@google-cloud/spanner/backup;;Member[Backup]", //
        "@google-cloud/spanner;BackupStatic;@google-cloud/spanner/backup;BackupStatic;", //
        "@google-cloud/spanner;BackupStatic;@google-cloud/spanner;;Member[Backup]", //
        "@google-cloud/spanner;BatchTransaction;@google-cloud/spanner/batch-transaction;BatchTransaction;", //
        "@google-cloud/spanner;Database;@google-cloud/spanner/database;Database;", //
        "@google-cloud/spanner;Database;@google-cloud/spanner/database;DatabaseCallback;Argument[1]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner/database;RestoreDatabaseCallback;Argument[1]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner/database;SessionPoolConstructor;Argument[0]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner/instance;CreateDatabaseCallback;Argument[1]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;DatabaseStatic;Instance", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;Instance;Member[database].ReturnValue", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;SessionPool;Member[database]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;SessionPoolStatic;Argument[0]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;SessionStatic;Argument[0]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;Table;Member[database]", //
        "@google-cloud/spanner;Database;@google-cloud/spanner;TableStatic;Argument[0]", //
        "@google-cloud/spanner;DatabaseStatic;@google-cloud/spanner/database;;Member[Database]", //
        "@google-cloud/spanner;DatabaseStatic;@google-cloud/spanner/database;DatabaseStatic;", //
        "@google-cloud/spanner;DatabaseStatic;@google-cloud/spanner;;Member[Database]", //
        "@google-cloud/spanner;GetInstancesCallback;@google-cloud/spanner/build/src;GetInstancesCallback;", //
        "@google-cloud/spanner;GetInstancesCallback;@google-cloud/spanner;Spanner;Member[getInstances].Argument[1]", //
        "@google-cloud/spanner;GetInstancesCallback;@google-cloud/spanner;Spanner;Member[getInstances].WithArity[1].Argument[0]", //
        "@google-cloud/spanner;GetInstancesResponse;@google-cloud/spanner/build/src;GetInstancesResponse;", //
        "@google-cloud/spanner;GetInstancesResponse;@google-cloud/spanner;Spanner;Member[getInstances].WithArity[0..1].ReturnValue.Awaited", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner/instance;CreateInstanceCallback;Argument[1]", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner/instance;GetInstanceCallback;Argument[1]", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner/instance;Instance;", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner;BackupStatic;Argument[0]", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner;DatabaseStatic;Argument[0]", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner;GetInstancesCallback;Argument[1].ArrayElement", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner;InstanceStatic;Instance", //
        "@google-cloud/spanner;Instance;@google-cloud/spanner;Spanner;Member[instance].ReturnValue", //
        "@google-cloud/spanner;InstanceStatic;@google-cloud/spanner/instance;;Member[Instance]", //
        "@google-cloud/spanner;InstanceStatic;@google-cloud/spanner/instance;InstanceStatic;", //
        "@google-cloud/spanner;InstanceStatic;@google-cloud/spanner;;Member[Instance]", //
        "@google-cloud/spanner;SessionPool;@google-cloud/spanner/instance;CreateDatabaseOptions;Member[poolCtor]", //
        "@google-cloud/spanner;SessionPool;@google-cloud/spanner/session-pool;SessionPool;", //
        "@google-cloud/spanner;SessionPool;@google-cloud/spanner;SessionPoolStatic;Instance", //
        "@google-cloud/spanner;SessionPoolStatic;@google-cloud/spanner/session-pool;;Member[SessionPool]", //
        "@google-cloud/spanner;SessionPoolStatic;@google-cloud/spanner/session-pool;SessionPoolStatic;", //
        "@google-cloud/spanner;SessionPoolStatic;@google-cloud/spanner;;Member[SessionPool]", //
        "@google-cloud/spanner;SessionStatic;@google-cloud/spanner/session;;Member[Session]", //
        "@google-cloud/spanner;SessionStatic;@google-cloud/spanner/session;SessionStatic;", //
        "@google-cloud/spanner;SessionStatic;@google-cloud/spanner;;Member[Session]", //
        "@google-cloud/spanner;Spanner;@google-cloud/spanner;InstanceStatic;Argument[0]", //
        "@google-cloud/spanner;Spanner;@google-cloud/spanner;SpannerStatic;Instance", //
        "@google-cloud/spanner;SpannerStatic;@google-cloud/spanner;;Member[Spanner]", //
        "@google-cloud/spanner;Table;@google-cloud/spanner/table;CreateTableCallback;Argument[1]", //
        "@google-cloud/spanner;Table;@google-cloud/spanner/table;Table;", //
        "@google-cloud/spanner;Table;@google-cloud/spanner;Database;Member[table].ReturnValue", //
        "@google-cloud/spanner;Table;@google-cloud/spanner;TableStatic;Instance", //
        "@google-cloud/spanner;TableStatic;@google-cloud/spanner/table;;Member[Table]", //
        "@google-cloud/spanner;TableStatic;@google-cloud/spanner/table;TableStatic;", //
        "@google-cloud/spanner;TableStatic;@google-cloud/spanner;;Member[Table]", //
      ]
  }
}
