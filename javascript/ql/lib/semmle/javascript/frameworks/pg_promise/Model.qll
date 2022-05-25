private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "pg-promise/typescript/pg-subset;pg.IClient;Member[query].Argument[0];sql-injection", //
        "pg-promise;IBaseProtocol;Member[any,each,many,manyOrNone,map,multi,multiResult,none,one,oneOrNone,query,result].Argument[0];sql-injection", //
        "pg-promise;IHelpers;Member[concat].Argument[0].ArrayElement.Member[query];sql-injection", //
        "pg-promise;IParameterizedQuery;Member[text];sql-injection", //
        "pg-promise;IPreparedStatement;Member[text];sql-injection", //
        "pg-promise;ParameterizedQuery;Member[text];sql-injection", //
        "pg-promise;PreparedStatement;Member[text];sql-injection", //
        "pg-promise;QueryFile;Member[file];sql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "pg-promise/typescript/pg-subset;;pg-promise/typescript/pg-subset;;", //
        "pg-promise/typescript/pg-subset;pg.IClient;pg-promise/typescript/pg-subset;;Member[Client].ReturnValue", //
        "pg-promise/typescript/pg-subset;pg.IClient;pg-promise;IMain;Member[pg].Member[Client].ReturnValue", //
        "pg-promise;;pg-promise/typescript/pg-promise;;", //
        "pg-promise;;pg-promise;;", //
        "pg-promise;IBaseProtocol;pg-promise/typescript/pg-promise;IBaseProtocol;", //
        "pg-promise;IBaseProtocol;pg-promise;IConnected;", //
        "pg-promise;IBaseProtocol;pg-promise;IDatabase;", //
        "pg-promise;IBaseProtocol;pg-promise;ITask;", //
        "pg-promise;IConnected;pg-promise/typescript/pg-promise;IConnected;", //
        "pg-promise;IConnected;pg-promise;IDatabase;Member[connect].ReturnValue.Awaited", //
        "pg-promise;IDatabase;pg-promise/typescript/pg-promise;IDatabase;", //
        "pg-promise;IDatabase;pg-promise;IInitOptions;Member[extend].Argument[0]", //
        "pg-promise;IDatabase;pg-promise;IMain;ReturnValue", //
        "pg-promise;IFormatting;pg-promise/typescript/pg-promise;;Member[as]", //
        "pg-promise;IFormatting;pg-promise/typescript/pg-promise;IFormatting;", //
        "pg-promise;IFormatting;pg-promise;;Member[as]", //
        "pg-promise;IFormatting;pg-promise;IMain;Member[as]", //
        "pg-promise;IHelpers;pg-promise/typescript/pg-promise;IHelpers;", //
        "pg-promise;IHelpers;pg-promise;IMain;Member[helpers]", //
        "pg-promise;IInitOptions;pg-promise/typescript/pg-promise;;Argument[0]", //
        "pg-promise;IInitOptions;pg-promise/typescript/pg-promise;IInitOptions;", //
        "pg-promise;IInitOptions;pg-promise;;Argument[0]", //
        "pg-promise;IInitOptions;pg-promise;ILibConfig;Member[options]", //
        "pg-promise;ILibConfig;pg-promise/typescript/pg-promise;ILibConfig;", //
        "pg-promise;ILibConfig;pg-promise;IDatabase;Member[$config]", //
        "pg-promise;IMain;pg-promise/typescript/pg-promise;;ReturnValue", //
        "pg-promise;IMain;pg-promise/typescript/pg-promise;IMain;", //
        "pg-promise;IMain;pg-promise;;ReturnValue", //
        "pg-promise;IMain;pg-promise;ILibConfig;Member[pgp]", //
        "pg-promise;IParameterizedQuery;pg-promise/typescript/pg-promise;IParameterizedQuery;", //
        "pg-promise;IParameterizedQuery;pg-promise;ParameterizedQueryStatic;Argument[0]", //
        "pg-promise;IParameterizedQuery;pg-promise;QueryParam;", //
        "pg-promise;IPreparedStatement;pg-promise/typescript/pg-promise;IPreparedStatement;", //
        "pg-promise;IPreparedStatement;pg-promise;PreparedStatementStatic;Argument[0]", //
        "pg-promise;IPreparedStatement;pg-promise;QueryParam;", //
        "pg-promise;ITask;pg-promise/typescript/pg-promise;ITask;", //
        "pg-promise;ITask;pg-promise;IBaseProtocol;Member[task,taskIf,tx,txIf].Argument[0,1].Argument[0]", //
        "pg-promise;ITask;pg-promise;IBaseProtocol;Member[taskIf].Argument[0].Member[cnd].Argument[0]", //
        "pg-promise;ITask;pg-promise;IBaseProtocol;Member[txIf].Argument[0].Member[cnd,reusable].Argument[0]", //
        "pg-promise;ParameterizedQuery;pg-promise/typescript/pg-promise;ParameterizedQuery;", //
        "pg-promise;ParameterizedQuery;pg-promise;ParameterizedQueryStatic;ReturnValue", //
        "pg-promise;ParameterizedQuery;pg-promise;QueryParam;", //
        "pg-promise;ParameterizedQueryStatic;pg-promise/typescript/pg-promise;;Member[ParameterizedQuery]", //
        "pg-promise;ParameterizedQueryStatic;pg-promise/typescript/pg-promise;ParameterizedQueryStatic;", //
        "pg-promise;ParameterizedQueryStatic;pg-promise;;Member[ParameterizedQuery]", //
        "pg-promise;ParameterizedQueryStatic;pg-promise;IMain;Member[ParameterizedQuery]", //
        "pg-promise;PreparedStatement;pg-promise/typescript/pg-promise;PreparedStatement;", //
        "pg-promise;PreparedStatement;pg-promise;PreparedStatementStatic;ReturnValue", //
        "pg-promise;PreparedStatement;pg-promise;QueryParam;", //
        "pg-promise;PreparedStatementStatic;pg-promise/typescript/pg-promise;;Member[PreparedStatement]", //
        "pg-promise;PreparedStatementStatic;pg-promise/typescript/pg-promise;PreparedStatementStatic;", //
        "pg-promise;PreparedStatementStatic;pg-promise;;Member[PreparedStatement]", //
        "pg-promise;PreparedStatementStatic;pg-promise;IMain;Member[PreparedStatement]", //
        "pg-promise;QueryFile;pg-promise/typescript/pg-promise;QueryFile;", //
        "pg-promise;QueryFile;pg-promise;IFormatting;Member[format].Argument[0]", //
        "pg-promise;QueryFile;pg-promise;IHelpers;Member[concat].Argument[0].ArrayElement", //
        "pg-promise;QueryFile;pg-promise;IHelpers;Member[concat].Argument[0].ArrayElement.Member[query]", //
        "pg-promise;QueryFile;pg-promise;IParameterizedQuery;Member[text]", //
        "pg-promise;QueryFile;pg-promise;IPreparedStatement;Member[text]", //
        "pg-promise;QueryFile;pg-promise;ParameterizedQuery;Member[text]", //
        "pg-promise;QueryFile;pg-promise;ParameterizedQueryStatic;Argument[0]", //
        "pg-promise;QueryFile;pg-promise;PreparedStatement;Member[text]", //
        "pg-promise;QueryFile;pg-promise;QueryFileStatic;ReturnValue", //
        "pg-promise;QueryFile;pg-promise;QueryParam;", //
        "pg-promise;QueryFileStatic;pg-promise/typescript/pg-promise;;Member[QueryFile]", //
        "pg-promise;QueryFileStatic;pg-promise/typescript/pg-promise;QueryFileStatic;", //
        "pg-promise;QueryFileStatic;pg-promise;;Member[QueryFile]", //
        "pg-promise;QueryFileStatic;pg-promise;IMain;Member[QueryFile]", //
        "pg-promise;QueryParam;pg-promise/typescript/pg-promise;QueryParam;", //
        "pg-promise;QueryParam;pg-promise;IBaseProtocol;Member[any,each,many,manyOrNone,map,multi,multiResult,none,one,oneOrNone,query,result].Argument[0]", //
        "pg-promise;QueryParam;pg-promise;QueryParam;ReturnValue", //
      ]
  }
}
