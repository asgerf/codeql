/**
 * Provides classes for working with NoSQL libraries.
 */

import javascript

/** Provides classes for modeling NoSql query sinks. */
module NoSql {
  /** An expression that is interpreted as a NoSql query. */
  abstract class Query extends Expr {
    /** Gets an expression that is interpreted as a code operator in this query. */
    DataFlow::Node getACodeOperator() { none() }
  }
}

/** DEPRECATED: Alias for NoSql */
deprecated module NoSQL = NoSql;

/**
 * Gets a value that has been assigned to the "$where" property of an object that flows to `queryArg`.
 */
private DataFlow::Node getADollarWhereProperty(API::Node queryArg) {
  result = queryArg.getMember("$where").asSink()
}

/**
 * Provides classes modeling the `mongodb` and `mongoose` libraries.
 */
private module MongoDB {
  private class OldMongoDbAdapter extends ModelInput::TypeModelCsv {
    override predicate row(string row) {
      // In Mongo version 2.x, a client and a database handle were the same concept, but in 3.x
      // they were separated. To handle everything with a single model, we treat them as the same here.
      row = "mongodb;Db;mongodb;MongoClient;"
    }
  }

  /** A call to a MongoDB query method. */
  private class QueryCall extends DatabaseAccess, API::CallNode {
    API::Node sink;

    QueryCall() {
      sink = ModelOutput::getASinkNode("mongodb.sink") and
      sink.asSink() = [this.getAnArgument(), this.getOptionArgument(_, _)]
    }

    override DataFlow::Node getAQueryArgument() { result = sink.asSink() }

    override DataFlow::Node getAResult() {
      PromiseFlow::loadStep(this.getALocalUse(), result, Promises::valueProp())
    }

    DataFlow::Node getACodeOperator() { result = sink.getMember("$where").asSink() }
  }

  /**
   * An expression that is interpreted as a MongoDB query.
   */
  class Query extends NoSql::Query {
    QueryCall qc;

    Query() { this = ModelOutput::getASinkNode("mongodb.sink").asSink().asExpr() }

    override DataFlow::Node getACodeOperator() { result = qc.getACodeOperator() }
  }

  private API::Node credentialsObject() {
    result = API::Node::ofType("mongodb", "Auth")
    or
    result = API::Node::ofType("mongoose", "ConnectOptions")
  }

  /**
   * An expression passed to `mongodb` or `mongoose` to supply credentials.
   */
  class Credentials extends CredentialsExpr {
    string kind;

    Credentials() {
      exists(string prop | this = credentialsObject().getMember(prop).asSink().asExpr() |
        prop = "user" and kind = "user name"
        or
        prop = "pass" and kind = "password"
      )
    }

    override string getCredentialsKind() { result = kind }
  }

  /**
   * Provides signatures for the Collection methods.
   *
   * NOTE: not currently used by the mongodb model itself, only the other models in this file
   */
  module CollectionMethodSignatures {
    /**
     * Holds if Collection method `name` interprets parameter `n` as a query.
     */
    predicate interpretsArgumentAsQuery(string name, int n) {
      // FilterQuery
      (
        name = "aggregate" and n = 0
        or
        name = "count" and n = 0
        or
        name = "countDocuments" and n = 0
        or
        name = "deleteMany" and n = 0
        or
        name = "deleteOne" and n = 0
        or
        name = "distinct" and n = 1
        or
        name = "find" and n = 0
        or
        name = "findOne" and n = 0
        or
        name = "findOneAndDelete" and n = 0
        or
        name = "findOneAndRemove" and n = 0
        or
        name = "findOneAndReplace" and n = 0
        or
        name = "findOneAndUpdate" and n = 0
        or
        name = "remove" and n = 0
        or
        name = "replaceOne" and n = 0
        or
        name = "update" and n = 0
        or
        name = "updateMany" and n = 0
        or
        name = "updateOne" and n = 0
      )
      or
      // UpdateQuery
      (
        name = "findOneAndUpdate" and n = 1
        or
        name = "update" and n = 1
        or
        name = "updateMany" and n = 1
        or
        name = "updateOne" and n = 1
      )
    }
  }
}

/**
 * Provides classes modeling the MarsDB library.
 */
private module MarsDB {
  private class MarsDBAccess extends DatabaseAccess, DataFlow::CallNode {
    string method;

    MarsDBAccess() {
      this =
        API::moduleImport("marsdb")
            .getMember("Collection")
            .getInstance()
            .getMember(method)
            .getACall()
    }

    string getMethod() { result = method }

    override DataFlow::Node getAResult() {
      PromiseFlow::loadStep(this.getALocalUse(), result, Promises::valueProp())
    }

    override DataFlow::Node getAQueryArgument() { none() }
  }

  /** A call to a MarsDB query method. */
  private class QueryCall extends MarsDBAccess, API::CallNode {
    int queryArgIdx;

    QueryCall() {
      exists(string m |
        this.getMethod() = m and
        // implements parts of the Minimongo interface
        Minimongo::CollectionMethodSignatures::interpretsArgumentAsQuery(m, queryArgIdx)
      )
    }

    override DataFlow::Node getAResult() {
      PromiseFlow::loadStep(this.getALocalUse(), result, Promises::valueProp())
    }

    override DataFlow::Node getAQueryArgument() { result = this.getArgument(queryArgIdx) }

    DataFlow::Node getACodeOperator() {
      result = getADollarWhereProperty(this.getParameter(queryArgIdx))
    }
  }

  /**
   * An expression that is interpreted as a MarsDB query.
   */
  class Query extends NoSql::Query {
    QueryCall qc;

    Query() { this = qc.getAQueryArgument().asExpr() }

    override DataFlow::Node getACodeOperator() { result = qc.getACodeOperator() }
  }
}

/**
 * Provides classes modeling the `Node Redis` library.
 *
 * Redis is an in-memory key-value store and not a database,
 * but `Node Redis` can be exploited similarly to a NoSQL database by giving a method an array as argument instead of a string.
 * As an example the below two invocations of `client.set` are equivalent:
 *
 * ```
 * const redis = require("redis");
 * const client = redis.createClient();
 * client.set("key", "value");
 * client.set(["key", "value"]);
 * ```
 *
 * ioredis is a very similar library. However, ioredis does not support array arguments in the same way, and is therefore not vulnerable to the same kind of type confusion.
 */
private module Redis {
  /**
   * Gets a `Node Redis` client.
   */
  private API::Node client() {
    result = API::moduleImport("redis").getMember("createClient").getReturn()
    or
    result = API::moduleImport("redis").getMember("RedisClient").getInstance()
    or
    result = client().getMember("duplicate").getReturn()
    or
    result = client().getMember("duplicate").getLastParameter().getParameter(1)
  }

  /**
   * Gets a (possibly chained) reference to a batch operation object.
   * These have the same API as a redis client, except the calls are chained, and the sequence is terminated with a `.exec` call.
   */
  private API::Node multi() {
    result = client().getMember(["multi", "batch"]).getReturn()
    or
    result = multi().getAMember().getReturn()
  }

  /**
   * Gets a `Node Redis` client instance. Either a client created using `createClient()`, or a batch operation object.
   */
  private API::Node redis() { result = [client(), multi()] }

  /**
   * Provides signatures for the query methods from Node Redis.
   */
  module QuerySignatures {
    /**
     * Holds if `method` interprets parameter `argIndex` as a key, and a later parameter determines a value/field.
     * Thereby the method is vulnerable if parameter `argIndex` is unexpectedly an array instead of a string, as an attacker can control arguments to Redis that the attacker was not supposed to control.
     *
     * Only setters and similar methods are included.
     * For getter-like methods it is not generally possible to gain access "outside" of where you are supposed to have access,
     * it is at most possible to get a Redis call to return more results than expected (e.g. by adding more members to [`geohash`](https://redis.io/commands/geohash)).
     */
    predicate argumentIsAmbiguousKey(string method, int argIndex) {
      method =
        [
          "set", "publish", "append", "bitfield", "decrby", "getset", "hincrby", "hincrbyfloat",
          "hset", "hsetnx", "incrby", "incrbyfloat", "linsert", "lpush", "lpushx", "lset", "ltrim",
          "rename", "renamenx", "rpushx", "setbit", "setex", "smove", "zincrby", "zinterstore",
          "hdel", "lpush", "pfadd", "rpush", "sadd", "sdiffstore", "srem"
        ] and
      argIndex = 0
      or
      method = ["bitop", "hmset", "mset", "msetnx", "geoadd"] and
      argIndex in [0 .. any(DataFlow::InvokeNode invk).getNumArgument() - 1]
    }
  }

  /**
   * An expression that is interpreted as a key in a Node Redis call.
   */
  class RedisKeyArgument extends NoSql::Query {
    RedisKeyArgument() {
      exists(string method, int argIndex |
        QuerySignatures::argumentIsAmbiguousKey(method, argIndex) and
        this = redis().getMember(method).getParameter(argIndex).asSink().asExpr()
      )
    }
  }

  /**
   * An access to a database through redis
   */
  class RedisDatabaseAccess extends DatabaseAccess, DataFlow::CallNode {
    RedisDatabaseAccess() { this = redis().getMember(_).getACall() }

    override DataFlow::Node getAResult() {
      PromiseFlow::loadStep(this.getALocalUse(), result, Promises::valueProp())
    }

    override DataFlow::Node getAQueryArgument() { none() }
  }
}

/**
 * Provides classes modeling the `ioredis` library.
 *
 * ```
 * import Redis from 'ioredis'
 * let client = new Redis(...)
 * ```
 */
private module IoRedis {
  /**
   * Gets an `ioredis` client.
   */
  API::Node ioredis() { result = API::moduleImport("ioredis").getInstance() }

  /**
   * An access to a database through ioredis
   */
  class IoRedisDatabaseAccess extends DatabaseAccess, DataFlow::CallNode {
    IoRedisDatabaseAccess() { this = ioredis().getMember(_).getACall() }

    override DataFlow::Node getAResult() {
      PromiseFlow::loadStep(this.getALocalUse(), result, Promises::valueProp())
    }

    override DataFlow::Node getAQueryArgument() { none() }
  }
}
