private import codeql.ruby.DataFlow
private import codeql.ruby.Concepts
private import codeql.ruby.frameworks.Sqlite3
private import codeql.ruby.security.SqlInjectionCustomizations

query predicate sqlite3SqlConstruction(SqlConstruction c, DataFlow::Node sql) { sql = c.getSql() }

query predicate sqlite3SqlExecution(SqlExecution e, DataFlow::Node sql) { sql = e.getSql() }

query predicate sqlinjectionSinks(SqlInjection::Sink sink) { any() }
