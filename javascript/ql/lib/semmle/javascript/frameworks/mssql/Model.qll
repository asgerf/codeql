private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "mssql/msnodesqlv8;;Member[query].Argument[0];sql-injection", //
        "mssql;;Member[query].Argument[0];sql-injection", //
        "mssql;ConnectionPool;Member[batch,query].Argument[0];sql-injection", //
        "mssql;Request;Member[execute,query].Argument[0];sql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "mssql;ConnectionPool;mssql/msnodesqlv8;;Member[connect].ReturnValue.Awaited", //
        "mssql;ConnectionPool;mssql/msnodesqlv8;;Member[pool]", //
        "mssql;ConnectionPool;mssql;;Member[connect].ReturnValue.Awaited", //
        "mssql;ConnectionPool;mssql;;Member[pool]", //
        "mssql;ConnectionPool;mssql;ConnectionPool;Member[connect].ReturnValue.Awaited", //
        "mssql;ConnectionPool;mssql;ConnectionPoolStatic;Instance", //
        "mssql;ConnectionPool;mssql;PreparedStatementStatic;Argument[0]", //
        "mssql;ConnectionPool;mssql;RequestStatic;Argument[0]", //
        "mssql;ConnectionPool;mssql;TransactionStatic;Argument[0]", //
        "mssql;ConnectionPoolStatic;mssql/msnodesqlv8;;Member[ConnectionPool]", //
        "mssql;ConnectionPoolStatic;mssql;;Member[ConnectionPool]", //
        "mssql;PreparedStatement;mssql;PreparedStatement;Member[input,output,prepare,unprepare].ReturnValue", //
        "mssql;PreparedStatement;mssql;PreparedStatementStatic;Instance", //
        "mssql;PreparedStatement;mssql;Request;Member[pstatement]", //
        "mssql;PreparedStatement;mssql;RequestStatic;Argument[0]", //
        "mssql;PreparedStatementStatic;mssql/msnodesqlv8;;Member[PreparedStatement]", //
        "mssql;PreparedStatementStatic;mssql;;Member[PreparedStatement]", //
        "mssql;Request;mssql;ConnectionPool;Member[request].ReturnValue", //
        "mssql;Request;mssql;PreparedStatement;Member[execute].ReturnValue", //
        "mssql;Request;mssql;Request;Member[input,output,replaceInput].ReturnValue", //
        "mssql;Request;mssql;RequestStatic;Instance", //
        "mssql;Request;mssql;Transaction;Member[request].ReturnValue", //
        "mssql;RequestStatic;mssql/msnodesqlv8;;Member[Request]", //
        "mssql;RequestStatic;mssql;;Member[Request]", //
        "mssql;Transaction;mssql;ConnectionPool;Member[transaction].ReturnValue", //
        "mssql;Transaction;mssql;PreparedStatement;Member[transaction]", //
        "mssql;Transaction;mssql;PreparedStatementStatic;Argument[0]", //
        "mssql;Transaction;mssql;Request;Member[transaction]", //
        "mssql;Transaction;mssql;RequestStatic;Argument[0]", //
        "mssql;Transaction;mssql;Transaction;Member[begin].ReturnValue", //
        "mssql;Transaction;mssql;Transaction;Member[begin].ReturnValue.Awaited", //
        "mssql;Transaction;mssql;TransactionStatic;Instance", //
        "mssql;TransactionStatic;mssql/msnodesqlv8;;Member[Transaction]", //
        "mssql;TransactionStatic;mssql;;Member[Transaction]", //
      ]
  }
}
