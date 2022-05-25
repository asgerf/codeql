private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "minimongo;HybridCollection;Member[find,findOne].Argument[0];nosql-injection", //
        "minimongo;MinimongoBaseCollection;Member[find,findOne].Argument[0];nosql-injection", //
        "minimongo;MinimongoCollectionFindOptions;Member[orderByExprs].ArrayElement.Member[expr];nosql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "minimongo/lib/HybridDb;HybridCollectionStatic;minimongo;;Member[HybridCollection]", //
        "minimongo/lib/HybridDb;default;minimongo/lib/HybridDb;defaultStatic;ReturnValue", //
        "minimongo/lib/HybridDb;defaultStatic;minimongo;;Member[HybridDb]", //
        "minimongo/lib/IndexedDb;IndexedDbCollection;minimongo/lib/IndexedDb;IndexedDbCollectionStatic;ReturnValue", //
        "minimongo/lib/IndexedDb;default;minimongo/lib/IndexedDb;defaultStatic;ReturnValue", //
        "minimongo/lib/IndexedDb;default;minimongo;;Member[utils].Member[autoselectLocalDb].ReturnValue", //
        "minimongo/lib/IndexedDb;defaultStatic;minimongo;;Member[IndexedDb]", //
        "minimongo/lib/LocalStorageDb;default;minimongo/lib/LocalStorageDb;defaultStatic;ReturnValue", //
        "minimongo/lib/LocalStorageDb;default;minimongo;;Member[utils].Member[autoselectLocalDb].ReturnValue", //
        "minimongo/lib/LocalStorageDb;defaultStatic;minimongo;;Member[LocalStorageDb]", //
        "minimongo/lib/MemoryDb;Collection;minimongo/lib/MemoryDb;CollectionStatic;ReturnValue", //
        "minimongo/lib/MemoryDb;default;minimongo/lib/MemoryDb;defaultStatic;ReturnValue", //
        "minimongo/lib/MemoryDb;default;minimongo;;Member[utils].Member[autoselectLocalDb].ReturnValue", //
        "minimongo/lib/MemoryDb;defaultStatic;minimongo;;Member[MemoryDb]", //
        "minimongo/lib/RemoteDb;Collection;minimongo/lib/RemoteDb;CollectionStatic;ReturnValue", //
        "minimongo/lib/RemoteDb;default;minimongo/lib/RemoteDb;defaultStatic;ReturnValue", //
        "minimongo/lib/RemoteDb;defaultStatic;minimongo;;Member[RemoteDb]", //
        "minimongo/lib/ReplicatingDb;Collection;minimongo/lib/ReplicatingDb;CollectionStatic;ReturnValue", //
        "minimongo/lib/ReplicatingDb;default;minimongo/lib/ReplicatingDb;defaultStatic;ReturnValue", //
        "minimongo/lib/ReplicatingDb;defaultStatic;minimongo;;Member[ReplicatingDb]", //
        "minimongo/lib/WebSQLDb;default;minimongo/lib/WebSQLDb;defaultStatic;ReturnValue", //
        "minimongo/lib/WebSQLDb;default;minimongo;;Member[utils].Member[autoselectLocalDb].ReturnValue", //
        "minimongo/lib/WebSQLDb;defaultStatic;minimongo;;Member[WebSQLDb]", //
        "minimongo;HybridCollection;minimongo/lib/HybridDb;HybridCollection;", //
        "minimongo;HybridCollection;minimongo/lib/HybridDb;HybridCollectionStatic;ReturnValue", //
        "minimongo;MinimongoBaseCollection;minimongo/lib/RemoteDb;Collection;", //
        "minimongo;MinimongoBaseCollection;minimongo/lib/types;MinimongoBaseCollection;", //
        "minimongo;MinimongoBaseCollection;minimongo;HybridCollection;", //
        "minimongo;MinimongoBaseCollection;minimongo;MinimongoCollection;", //
        "minimongo;MinimongoBaseCollection;minimongo;MinimongoLocalCollection;", //
        "minimongo;MinimongoCollection;minimongo/lib/HybridDb;HybridCollectionStatic;Argument[2]", //
        "minimongo;MinimongoCollection;minimongo/lib/types;MinimongoCollection;", //
        "minimongo;MinimongoCollection;minimongo;HybridCollection;Member[remoteCol]", //
        "minimongo;MinimongoCollectionFindOptions;minimongo/lib/IndexedDb;IndexedDbCollection;Member[find].Argument[1]", //
        "minimongo;MinimongoCollectionFindOptions;minimongo/lib/MemoryDb;Collection;Member[find].Argument[1]", //
        "minimongo;MinimongoCollectionFindOptions;minimongo/lib/RemoteDb;Collection;Member[_findFetch,find].Argument[1]", //
        "minimongo;MinimongoCollectionFindOptions;minimongo/lib/types;MinimongoCollectionFindOptions;", //
        "minimongo;MinimongoCollectionFindOptions;minimongo;MinimongoBaseCollection;Member[find].Argument[1]", //
        "minimongo;MinimongoDb;minimongo/lib/HybridDb;default;", //
        "minimongo;MinimongoDb;minimongo/lib/HybridDb;default;Member[remoteDb]", //
        "minimongo;MinimongoDb;minimongo/lib/HybridDb;defaultStatic;Argument[1]", //
        "minimongo;MinimongoDb;minimongo/lib/LocalStorageDb;default;", //
        "minimongo;MinimongoDb;minimongo/lib/MemoryDb;default;", //
        "minimongo;MinimongoDb;minimongo/lib/RemoteDb;default;", //
        "minimongo;MinimongoDb;minimongo/lib/ReplicatingDb;default;Member[masterDb,replicaDb]", //
        "minimongo;MinimongoDb;minimongo/lib/ReplicatingDb;defaultStatic;Argument[0,1]", //
        "minimongo;MinimongoDb;minimongo/lib/WebSQLDb;default;", //
        "minimongo;MinimongoDb;minimongo/lib/types;MinimongoDb;", //
        "minimongo;MinimongoDb;minimongo;;Member[utils].Member[cloneLocalDb].Argument[0,1]", //
        "minimongo;MinimongoDb;minimongo;MinimongoDb;Member[remoteDb]", //
        "minimongo;MinimongoDb;minimongo;MinimongoLocalDb;", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/HybridDb;HybridCollectionStatic;Argument[1]", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/IndexedDb;IndexedDbCollection;", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/MemoryDb;Collection;", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/ReplicatingDb;Collection;", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/ReplicatingDb;Collection;Member[masterCol,replicaCol]", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/ReplicatingDb;CollectionStatic;Argument[1,2]", //
        "minimongo;MinimongoLocalCollection;minimongo/lib/types;MinimongoLocalCollection;", //
        "minimongo;MinimongoLocalCollection;minimongo;;Member[utils].Member[cloneLocalCollection].Argument[0,1]", //
        "minimongo;MinimongoLocalCollection;minimongo;HybridCollection;Member[localCol]", //
        "minimongo;MinimongoLocalCollection;minimongo;MinimongoCollection;", //
        "minimongo;MinimongoLocalCollection;minimongo;MinimongoLocalDb;Member[addCollection].Argument[2].Argument[0]", //
        "minimongo;MinimongoLocalDb;minimongo/lib/HybridDb;default;Member[localDb]", //
        "minimongo;MinimongoLocalDb;minimongo/lib/HybridDb;defaultStatic;Argument[0]", //
        "minimongo;MinimongoLocalDb;minimongo/lib/IndexedDb;default;", //
        "minimongo;MinimongoLocalDb;minimongo/lib/ReplicatingDb;default;", //
        "minimongo;MinimongoLocalDb;minimongo/lib/types;MinimongoLocalDb;", //
        "minimongo;MinimongoLocalDb;minimongo;MinimongoDb;Member[localDb]", //
      ]
  }
}
