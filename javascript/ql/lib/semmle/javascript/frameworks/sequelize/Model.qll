private import javascript

private class Sinks extends ModelInput::SinkModelCsv {
  override predicate row(string row) {
    row =
      [
        "sequelize;Sequelize;Member[query].Argument[0].Member[query];sql-injection", //
        "sequelize;Sequelize;Member[query].Argument[0];sql-injection", //
        "sequelize;SequelizeStaticAndInstance;Member[asIs,literal].Argument[0];sql-injection", //
      ]
  }
}

private class Types extends ModelInput::TypeModelCsv {
  override predicate row(string row) {
    row =
      [
        "sequelize;AssociationOptionsBelongsToMany;sequelize;Associations;Member[belongsToMany].Argument[1]", //
        "sequelize;Associations;sequelize;Model;", //
        "sequelize;BuildOptions;sequelize;CreateOptions;", //
        "sequelize;BuildOptions;sequelize;Model;Member[build,bulkBuild].Argument[1]", //
        "sequelize;CountOptions;sequelize;Model;Member[count].Argument[0]", //
        "sequelize;CreateOptions;sequelize;BelongsToCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;BelongsToManyCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;HasManyCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;HasOneCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;Model;Member[create].Argument[1]", //
        "sequelize;DefineAttributeColumnOptions;sequelize;QueryInterface;Member[addColumn,changeColumn].Argument[2]", //
        "sequelize;DefineAttributeColumnReferencesOptions;sequelize;DefineAttributeColumnOptions;Member[references]", //
        "sequelize;FindCreateFindOptions;sequelize;Model;Member[findCreateFind].Argument[0]", //
        "sequelize;FindOptions;sequelize;FindCreateFindOptions;", //
        "sequelize;FindOptions;sequelize;FindOrInitializeOptions;", //
        "sequelize;FindOptions;sequelize;Model;Member[all,find,findAll,findAndCount,findAndCountAll,findOne].Argument[0]", //
        "sequelize;FindOrInitializeOptions;sequelize;Model;Member[findOrBuild,findOrCreate,findOrInitialize].Argument[0]", //
        "sequelize;HasManyGetAssociationsMixinOptions;sequelize;HasManyGetAssociationsMixin;Argument[0]", //
        "sequelize;HasManyGetAssociationsMixinOptions;sequelize;HasManyHasAssociationMixin;Argument[1]", //
        "sequelize;HasManyGetAssociationsMixinOptions;sequelize;HasManyHasAssociationsMixin;Argument[1]", //
        "sequelize;Hooks;sequelize;Hooks;Member[addHook,hook,removeHook].ReturnValue", //
        "sequelize;Hooks;sequelize;Model;", //
        "sequelize;Hooks;sequelize;Sequelize;", //
        "sequelize;IncludeAssociation;sequelize;Associations;Member[belongsTo,belongsToMany,hasMany,hasOne].ReturnValue", //
        "sequelize;IncludeAssociation;sequelize;IncludeOptions;Member[association]", //
        "sequelize;IncludeOptions;sequelize;BuildOptions;Member[include].ArrayElement", //
        "sequelize;IncludeOptions;sequelize;CountOptions;Member[include]", //
        "sequelize;IncludeOptions;sequelize;CountOptions;Member[include].ArrayElement", //
        "sequelize;IncludeOptions;sequelize;FindOptions;Member[include]", //
        "sequelize;IncludeOptions;sequelize;FindOptions;Member[include].ArrayElement", //
        "sequelize;IncludeOptions;sequelize;HasManyGetAssociationsMixinOptions;Member[include]", //
        "sequelize;IncludeOptions;sequelize;IncludeOptions;Member[include]", //
        "sequelize;IncludeOptions;sequelize;IncludeOptions;Member[include].ArrayElement", //
        "sequelize;Instance;sequelize;Instance;Member[equalsOneOf].Argument[0].ArrayElement", //
        "sequelize;Instance;sequelize;Instance;Member[equals].Argument[0]", //
        "sequelize;Instance;sequelize;QueryInterface;Member[delete,increment,insert,update].Argument[0]", //
        "sequelize;Instance;sequelize;QueryOptions;Member[instance]", //
        "sequelize;Instance;sequelize;SequelizeStaticAndInstance;Member[Instance]", //
        "sequelize;Model;sequelize;AssociationOptionsBelongsToMany;Member[through]", //
        "sequelize;Model;sequelize;Associations;Member[belongsTo,belongsToMany,hasMany,hasOne].Argument[0]", //
        "sequelize;Model;sequelize;BuildOptions;Member[include].ArrayElement", //
        "sequelize;Model;sequelize;CountOptions;Member[include]", //
        "sequelize;Model;sequelize;CountOptions;Member[include].ArrayElement", //
        "sequelize;Model;sequelize;DefineAttributeColumnReferencesOptions;Member[model]", //
        "sequelize;Model;sequelize;FindOptions;Member[include]", //
        "sequelize;Model;sequelize;FindOptions;Member[include].ArrayElement", //
        "sequelize;Model;sequelize;FindOptions;Member[lock].Member[of]", //
        "sequelize;Model;sequelize;Hooks;Member[afterDefine].Argument[0,1].Argument[0]", //
        "sequelize;Model;sequelize;IncludeAssociation;Member[source,target]", //
        "sequelize;Model;sequelize;IncludeOptions;Member[include,model]", //
        "sequelize;Model;sequelize;IncludeOptions;Member[include].ArrayElement", //
        "sequelize;Model;sequelize;Instance;Member[Model]", //
        "sequelize;Model;sequelize;QueryInterface;Member[bulkDelete,rawSelect,upsert].Argument[3]", //
        "sequelize;Model;sequelize;QueryInterface;Member[select].Argument[0]", //
        "sequelize;Model;sequelize;QueryOptions;Member[model]", //
        "sequelize;Model;sequelize;Sequelize;Member[define,import,model].ReturnValue", //
        "sequelize;Model;sequelize;Sequelize;Member[import].Argument[1].ReturnValue", //
        "sequelize;Model;sequelize;SequelizeStaticAndInstance;Member[Model]", //
        "sequelize;Model;sequelize;ThroughOptions;Member[model]", //
        "sequelize;Model;sequelize;Utils;Member[mapOptionFieldNames].Argument[1]", //
        "sequelize;Model;sequelize;Utils;Member[mapValueFieldNames].Argument[2]", //
        "sequelize;Options;sequelize;Sequelize;Member[options]", //
        "sequelize;Options;sequelize;SequelizeStatic;Argument[0,1,2,3]", //
        "sequelize;QueryInterface;sequelize;Sequelize;Member[getQueryInterface].ReturnValue", //
        "sequelize;QueryOptions;sequelize;Options;Member[query]", //
        "sequelize;QueryOptions;sequelize;QueryInterface;Member[bulkDelete,bulkInsert,createTable,select,setAutocommit,setIsolationLevel].Argument[2]", //
        "sequelize;QueryOptions;sequelize;QueryInterface;Member[bulkUpdate,delete,insert].Argument[3]", //
        "sequelize;QueryOptions;sequelize;QueryInterface;Member[commitTransaction,deferConstraints,dropTable,rawSelect,rollbackTransaction,showIndex,startTransaction].Argument[1]", //
        "sequelize;QueryOptions;sequelize;QueryInterface;Member[createFunction].Argument[5]", //
        "sequelize;QueryOptions;sequelize;QueryInterface;Member[dropAllEnums,dropAllTables,showAllSchemas,showAllTables].Argument[0]", //
        "sequelize;QueryOptions;sequelize;QueryInterface;Member[increment,update,upsert].Argument[4]", //
        "sequelize;QueryOptions;sequelize;Sequelize;Member[authenticate,validate].Argument[0]", //
        "sequelize;QueryOptions;sequelize;Sequelize;Member[query].Argument[1]", //
        "sequelize;Sequelize;sequelize;Hooks;Member[afterInit].Argument[0,1].Argument[0]", //
        "sequelize;Sequelize;sequelize;Instance;Member[sequelize]", //
        "sequelize;Sequelize;sequelize;QueryInterface;Member[sequelize]", //
        "sequelize;Sequelize;sequelize;Sequelize;Member[import].Argument[1].Argument[0]", //
        "sequelize;Sequelize;sequelize;SequelizeStatic;Member[useCLS].ReturnValue", //
        "sequelize;Sequelize;sequelize;SequelizeStatic;ReturnValue", //
        "sequelize;SequelizeStatic;sequelize;;", //
        "sequelize;SequelizeStatic;sequelize;Sequelize;Member[Sequelize]", //
        "sequelize;SequelizeStatic;sequelize;SequelizeStatic;Member[Sequelize,default]", //
        "sequelize;SequelizeStaticAndInstance;sequelize;Sequelize;", //
        "sequelize;SequelizeStaticAndInstance;sequelize;SequelizeStatic;", //
        "sequelize;ThroughOptions;sequelize;AssociationOptionsBelongsToMany;Member[through]", //
        "sequelize;Utils;sequelize;SequelizeStaticAndInstance;Member[Utils]", //
      ]
  }
}
