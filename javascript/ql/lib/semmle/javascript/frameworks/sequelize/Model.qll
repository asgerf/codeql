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
        "sequelize-typescript/dist/associations/belongs-to-many/belongs-to-many-association;BelongsToManyAssociationStatic;sequelize-typescript;;Member[BelongsToManyAssociation]", //
        "sequelize-typescript/dist/associations/belongs-to/belongs-to-association;BelongsToAssociationStatic;sequelize-typescript;;Member[BelongsToAssociation]", //
        "sequelize-typescript/dist/associations/has/has-association;HasAssociationStatic;sequelize-typescript;;Member[HasAssociation]", //
        "sequelize-typescript/dist/associations/shared/base-association;BaseAssociationStatic;sequelize-typescript;;Member[BaseAssociation]", //
        "sequelize-typescript/dist/model/model/association/association-create-options;AssociationCreateOptions;sequelize-typescript;Model;Member[$create].Argument[2]", //
        "sequelize-typescript/dist/model/model/model;ModelStatic~;sequelize-typescript/dist/model/shared/model-not-initialized-error;ModelNotInitializedErrorStatic;Argument[0]", //
        "sequelize-typescript/dist/model/model/model;ModelStatic~;sequelize-typescript;;Member[Model]", //
        "sequelize-typescript/dist/sequelize/sequelize/sequelize;SequelizeStatic;sequelize-typescript;;Member[Sequelize]", //
        "sequelize-typescript;AssociationCountOptions;sequelize-typescript/dist/model/model/association/association-count-options;AssociationCountOptions;", //
        "sequelize-typescript;AssociationCountOptions;sequelize-typescript;Model;Member[$count].Argument[1]", //
        "sequelize-typescript;AssociationGetOptions;sequelize-typescript/dist/model/model/association/association-get-options;AssociationGetOptions;", //
        "sequelize-typescript;AssociationGetOptions;sequelize-typescript;Model;Member[$get].Argument[1]", //
        "sequelize-typescript;AssociationGetOptions;sequelize-typescript;Model;Member[$has].Argument[2]", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript/dist/associations/shared/base-association;BaseAssociation;", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript/dist/associations/shared/base-association;BaseAssociationStatic;ReturnValue", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript;;Member[addAssociation].Argument[1]", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript;;Member[getAssociations,getAssociationsByRelation].ReturnValue.ArrayElement", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript;;Member[setAssociations].Argument[1].ArrayElement", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript;BelongsToAssociation;", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript;BelongsToManyAssociation;", //
        "sequelize-typescript;BaseAssociation;sequelize-typescript;HasAssociation;", //
        "sequelize-typescript;BelongsToAssociation;sequelize-typescript/dist/associations/belongs-to/belongs-to-association;BelongsToAssociation;", //
        "sequelize-typescript;BelongsToAssociation;sequelize-typescript/dist/associations/belongs-to/belongs-to-association;BelongsToAssociationStatic;ReturnValue", //
        "sequelize-typescript;BelongsToManyAssociation;sequelize-typescript/dist/associations/belongs-to-many/belongs-to-many-association;BelongsToManyAssociation;", //
        "sequelize-typescript;BelongsToManyAssociation;sequelize-typescript/dist/associations/belongs-to-many/belongs-to-many-association;BelongsToManyAssociationStatic;ReturnValue", //
        "sequelize-typescript;DefaultScopeGetter;sequelize-typescript/dist/scopes/scope-options;DefaultScopeGetter;", //
        "sequelize-typescript;DefaultScopeGetter;sequelize-typescript;;Member[DefaultScope].Argument[0]", //
        "sequelize-typescript;DefaultScopeGetter;sequelize-typescript;ScopeOptionsGetters;Member[getDefaultScope]", //
        "sequelize-typescript;HasAssociation;sequelize-typescript/dist/associations/has/has-association;HasAssociation;", //
        "sequelize-typescript;HasAssociation;sequelize-typescript/dist/associations/has/has-association;HasAssociationStatic;ReturnValue", //
        "sequelize-typescript;Model;sequelize-typescript/dist/model/model/model;Model;", //
        "sequelize-typescript;Model;sequelize-typescript/dist/model/model/model;ModelStatic~;ReturnValue", //
        "sequelize-typescript;Model;sequelize-typescript;ModelType;ReturnValue", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript/dist/associations/belongs-to-many/belongs-to-many-association;BelongsToManyAssociationStatic;Argument[0]", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript/dist/associations/belongs-to/belongs-to-association;BelongsToAssociationStatic;Argument[0]", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript/dist/associations/foreign-key/foreign-key-meta;ForeignKeyMeta;Member[relatedClassGetter]", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript/dist/associations/has/has-association;HasAssociationStatic;Argument[0]", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript/dist/associations/shared/base-association;BaseAssociationStatic;Argument[0]", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript/dist/model/shared/model-class-getter;ModelClassGetter;", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript;;Member[BelongsTo,ForeignKey,HasMany,HasOne].Argument[0]", //
        "sequelize-typescript;ModelClassGetter;sequelize-typescript;;Member[BelongsToMany].Argument[0,1]", //
        "sequelize-typescript;ModelCtor;sequelize-typescript/dist/model/model/model;ModelCtor;", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;;Member[getModels,installHooks,resolveScopes].Argument[0].ArrayElement", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;;Member[getModels].ReturnValue.ArrayElement", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;;Member[resolveScope].Argument[1]", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;;Member[resolvesDeprecatedScopes].Argument[0]", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;Sequelize;Member[addModels].Argument[0].ArrayElement", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;Sequelize;Member[model].ReturnValue", //
        "sequelize-typescript;ModelCtor;sequelize-typescript;SequelizeOptions;Member[models].ArrayElement", //
        "sequelize-typescript;ModelType;sequelize-typescript/dist/model/model/model;ModelType;", //
        "sequelize-typescript;ModelType;sequelize-typescript;BaseAssociation;Member[getAssociatedClass].ReturnValue", //
        "sequelize-typescript;ModelType;sequelize-typescript;BaseAssociation;Member[getSequelizeOptions].Argument[0]", //
        "sequelize-typescript;ModelType;sequelize-typescript;BelongsToAssociation;Member[getSequelizeOptions].Argument[0]", //
        "sequelize-typescript;ModelType;sequelize-typescript;BelongsToManyAssociation;Member[getSequelizeOptions].Argument[0]", //
        "sequelize-typescript;ModelType;sequelize-typescript;HasAssociation;Member[getSequelizeOptions].Argument[0]", //
        "sequelize-typescript;ModelType;sequelize-typescript;ModelClassGetter;ReturnValue", //
        "sequelize-typescript;ModelType;sequelize-typescript;Sequelize;Member[model].Argument[0]", //
        "sequelize-typescript;Repository;sequelize-typescript/dist/sequelize/repository/repository;Repository;", //
        "sequelize-typescript;Repository;sequelize-typescript;ModelCtor;", //
        "sequelize-typescript;Repository;sequelize-typescript;Sequelize;Member[getRepository].ReturnValue", //
        "sequelize-typescript;ScopeOptionsGetters;sequelize-typescript/dist/scopes/scope-options;ScopeOptionsGetters;", //
        "sequelize-typescript;ScopeOptionsGetters;sequelize-typescript;;Member[addScopeOptionsGetter,setScopeOptionsGetters].Argument[1]", //
        "sequelize-typescript;ScopeOptionsGetters;sequelize-typescript;;Member[getScopeOptionsGetters].ReturnValue", //
        "sequelize-typescript;ScopesOptions;sequelize-typescript/dist/scopes/scope-options;ScopesOptions;", //
        "sequelize-typescript;ScopesOptions;sequelize-typescript;;Member[resolveScope].Argument[2]", //
        "sequelize-typescript;Sequelize;sequelize-typescript/dist/sequelize/sequelize/sequelize;Sequelize;", //
        "sequelize-typescript;Sequelize;sequelize-typescript/dist/sequelize/sequelize/sequelize;SequelizeStatic;ReturnValue", //
        "sequelize-typescript;Sequelize;sequelize-typescript;BaseAssociation;Member[getSequelizeOptions].Argument[1]", //
        "sequelize-typescript;Sequelize;sequelize-typescript;BelongsToManyAssociation;Member[getSequelizeOptions].Argument[1]", //
        "sequelize-typescript;SequelizeOptions;sequelize-typescript/dist/sequelize/sequelize/sequelize-options;SequelizeOptions;", //
        "sequelize-typescript;SequelizeOptions;sequelize-typescript/dist/sequelize/sequelize/sequelize;SequelizeStatic;Argument[0,1,2,3]", //
        "sequelize-typescript;SequelizeOptions;sequelize-typescript;;Member[prepareArgs].ReturnValue.Member[options]", //
        "sequelize-typescript;SequelizeOptions;sequelize-typescript;;Member[prepareOptions].Argument[0]", //
        "sequelize-typescript;SequelizeOptions;sequelize-typescript;;Member[prepareOptions].ReturnValue", //
        "sequelize-typescript;SequelizeOptions;sequelize-typescript;Sequelize;Member[options]", //
        "sequelize;AnyFindOptions;sequelize;BelongsToManyAddAssociationMixin;Argument[1]", //
        "sequelize;AnyFindOptions;sequelize;BelongsToManyAddAssociationsMixin;Argument[1]", //
        "sequelize;AnyFindOptions;sequelize;BelongsToManySetAssociationsMixin;Argument[1]", //
        "sequelize;AnyFindOptions;sequelize;DefineOptions;Member[defaultScope]", //
        "sequelize;AnyFindOptions;sequelize;HasManySetAssociationsMixin;Argument[1]", //
        "sequelize;AnyFindOptions;sequelize;Instance;Member[reload].Argument[0]", //
        "sequelize;AnyFindOptions;sequelize;Model;Member[addScope].Argument[1]", //
        "sequelize;AssociationOptionsBelongsToMany;sequelize;Associations;Member[belongsToMany].Argument[1]", //
        "sequelize;Associations;sequelize;Model;", //
        "sequelize;BuildOptions;sequelize-typescript/dist/model/model/model;ModelStatic~;Argument[1]", //
        "sequelize;BuildOptions;sequelize;CreateOptions;", //
        "sequelize;BuildOptions;sequelize;Model;Member[build,bulkBuild].Argument[1]", //
        "sequelize;CountOptions;sequelize;Model;Member[count].Argument[0]", //
        "sequelize;CreateOptions;sequelize-typescript/dist/model/model/association/association-create-options;AssociationCreateOptions;", //
        "sequelize;CreateOptions;sequelize;BelongsToCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;BelongsToManyCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;HasManyCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;HasOneCreateAssociationMixin;Argument[1]", //
        "sequelize;CreateOptions;sequelize;Model;Member[create].Argument[1]", //
        "sequelize;DefineAttributeColumnOptions;sequelize;QueryInterface;Member[addColumn,changeColumn].Argument[2]", //
        "sequelize;DefineAttributeColumnReferencesOptions;sequelize;DefineAttributeColumnOptions;Member[references]", //
        "sequelize;DefineOptions;sequelize;Options;Member[define]", //
        "sequelize;DefineOptions;sequelize;Sequelize;Member[define].Argument[2]", //
        "sequelize;FindCreateFindOptions;sequelize;Model;Member[findCreateFind].Argument[0]", //
        "sequelize;FindOptions;sequelize-typescript;AssociationCountOptions;", //
        "sequelize;FindOptions;sequelize-typescript;AssociationGetOptions;", //
        "sequelize;FindOptions;sequelize-typescript;DefaultScopeGetter;ReturnValue", //
        "sequelize;FindOptions;sequelize-typescript;Model;Member[reload].Argument[0]", //
        "sequelize;FindOptions;sequelize-typescript;ScopesOptions;", //
        "sequelize;FindOptions;sequelize-typescript;ScopesOptions;ReturnValue", //
        "sequelize;FindOptions;sequelize;AnyFindOptions;", //
        "sequelize;FindOptions;sequelize;FindCreateFindOptions;", //
        "sequelize;FindOptions;sequelize;FindOrInitializeOptions;", //
        "sequelize;FindOptions;sequelize;Model;Member[all,find,findAll,findAndCount,findAndCountAll,findOne].Argument[0]", //
        "sequelize;FindOptionsOrderArray;sequelize;FindOptions;Member[order]", //
        "sequelize;FindOptionsOrderArray;sequelize;FindOptions;Member[order].ArrayElement", //
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
        "sequelize;Model;sequelize;FindOptionsOrderArray;ArrayElement", //
        "sequelize;Model;sequelize;FindOptionsOrderArray;ArrayElement.Member[model]", //
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
        "sequelize;Options;sequelize-typescript;SequelizeOptions;", //
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
        "sequelize;SequelizeStatic;sequelize-typescript;Sequelize;", //
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
