private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "mongodb;Collection;Member[count,countDocuments,deleteMany,deleteOne,find,findOne,findOneAndDelete,findOneAndReplace,findOneAndUpdate,remove,replaceOne,updateMany].Argument[0];nosql-injection", //
        "mongodb;Collection;Member[distinct].Argument[1];nosql-injection", //
        "mongodb;Collection;Member[update,updateOne].Argument[0,1];nosql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "mongodb;Collection;mongodb;Collection;Member[rename].Argument[1,2].Argument[1]", //
        "mongodb;Collection;mongodb;Collection;Member[rename].ReturnValue.Awaited", //
        "mongodb;Collection;mongodb;Db;Member[collection,createCollection].Argument[1,2].Argument[1]", //
        "mongodb;Collection;mongodb;Db;Member[collection].ReturnValue", //
        "mongodb;Collection;mongodb;Db;Member[collections].Argument[0].Argument[1].ArrayElement", //
        "mongodb;Collection;mongodb;Db;Member[collections].ReturnValue.Awaited.ArrayElement", //
        "mongodb;Collection;mongodb;Db;Member[createCollection,renameCollection].ReturnValue.Awaited", //
        "mongodb;Collection;mongodb;Db;Member[renameCollection].Argument[2,3].Argument[1]", //
        "mongodb;Collection;mongodb;GridFSBucketReadStreamStatic;Argument[0,1]", //
        "mongodb;Db;mongodb;;Member[connect].Argument[1,2].Argument[1]", //
        "mongodb;Db;mongodb;;Member[connect].ReturnValue.Awaited", //
        "mongodb;Db;mongodb;Db;Member[db].ReturnValue", //
        "mongodb;Db;mongodb;Db;Member[open].Argument[0].Argument[1]", //
        "mongodb;Db;mongodb;Db;Member[open].ReturnValue.Awaited", //
        "mongodb;Db;mongodb;DbStatic;ReturnValue", //
        "mongodb;Db;mongodb;GridFSBucketStatic;Argument[0]", //
        "mongodb;Db;mongodb;MongoClient;Member[connect].Argument[1,2].Argument[1]", //
        "mongodb;Db;mongodb;MongoClient;Member[connect].ReturnValue.Awaited", //
        "mongodb;Db;mongodb;MongoClientStatic;Member[connect].Argument[1,2].Argument[1]", //
        "mongodb;Db;mongodb;MongoClientStatic;Member[connect].ReturnValue.Awaited", //
        "mongodb;DbStatic;mongodb;;Member[Db]", //
        "mongodb;GridFSBucketReadStreamStatic;mongodb;;Member[GridFSBucketReadStream]", //
        "mongodb;GridFSBucketStatic;mongodb;;Member[GridFSBucket]", //
        "mongodb;MongoClient;mongodb;MongoClientStatic;ReturnValue", //
        "mongodb;MongoClientStatic;mongodb;;Member[MongoClient]", //
      ]
  }
}
