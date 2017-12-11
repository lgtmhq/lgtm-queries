// Copyright 2017 Semmle Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under
// the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

/**
 * Provides classes for working with SQL connectors.
 */

import javascript

module SQL {
  /** A string-valued expression that is interpreted as a SQL command. */
  abstract class SqlString extends Expr {
  }

  /**
   * An expression that sanitizes a string to make it safe to embed into
   * a SQL command.
   */
  abstract class SqlSanitizer extends Expr {
    Expr input;
    Expr output;

    /** Gets the input expression being sanitized. */
    Expr getInput() {
      result = input
    }

    /** Gets the output expression containing the sanitized value. */
    Expr getOutput() {
      result = output
    }
  }
}

/**
 * Provides classes modelling the `mysql` package.
 */
private module MySql {
  /** Holds if `nd` may contain an import of the `mysql` package. */
  predicate isMySql(DataFlowNode nd) {
    nd.getALocalSource().(ModuleInstance).getPath() = "mysql"
  }

  /** Gets a call to `mysql.createConnection`. */
  CallExpr createConnection() {
    exists (ModuleInstance mysql | mysql.getPath() = "mysql" |
      result = mysql.getAMethodCall("createConnection")
    )
  }

  /** Gets a call to `mysql.createPool`. */
  CallExpr createPool() {
    exists (ModuleInstance mysql | mysql.getPath() = "mysql" |
      result = mysql.getAMethodCall("createPool")
    )
  }

  /** Holds if `nd` may contain a MySQL connection instance. */
  predicate isConnection(DataFlowNode nd) {
    nd.getALocalSource() = createConnection()
    or
    exists (DataFlowNode pool, MethodCallExpr getConn, Function cb |
      isPool(pool) and getConn.calls(pool, "getConnection") and
      cb = getConn.getArgument(0).(DataFlowNode).getALocalSource() and
      nd.getALocalSource() = cb.getParameter(1).(SimpleParameter).getVariable().getAnAccess()
    )
  }

  /** Holds if `nd` may contain a MySQL pool instance. */
  predicate isPool(DataFlowNode nd) {
    nd.getALocalSource() = createPool()
  }

  /** An expression that is passed to the `query` method and hence interpreted as SQL. */
  class QueryString extends SQL::SqlString {
    QueryString() {
      exists (DataFlowNode base, MethodCallExpr mce |
        isConnection(base) or isPool(base) |
        mce.calls(base, "query") and this = mce.getArgument(0)
      )
    }
  }

  /** A call to the `escape` or `escapeId` method that performs SQL sanitization. */
  class EscapingSanitizer extends SQL::SqlSanitizer, @callexpr {
    EscapingSanitizer() {
      exists (DataFlowNode base, MethodCallExpr mce, string esc |
        isMySql(base) or isConnection(base) or isPool(base) |
        this = mce and mce.calls(base, esc) and
        (esc = "escape" or esc = "escapeId") and
        input = mce.getArgument(0) and
        output = mce
      )
    }
  }

  /** An expression that is passed as user name or password to `mysql.createConnection`. */
  class Credentials extends CredentialsExpr {
    string kind;

    Credentials() {
      exists (CallExpr call, string prop |
        (call = createConnection() or call = createPool())
        and
        call.hasOptionArgument(0, prop, this)
        and
        (
          prop = "user" and kind = "user name" or
          prop = "password" and kind = prop
        )
      )
    }

    override string getCredentialsKind() {
      result = kind
    }
  }
}

/**
 * Provides classes modelling the `pg` package.
 */
private module Postgres {
  /** Gets an expression of the form `new require('pg').Client()`. */
  NewExpr newClient() {
    exists (ModuleInstance pg, PropReadNode pgClient |
      pg.getPath() = "pg" and
      pgClient.getBase().getALocalSource() = pg and pgClient.getPropertyName() = "Client" and
      result.getCallee().(DataFlowNode).getALocalSource() = pgClient
    )
  }

  /** Holds if `nd` may contain a Postgres client instance. */
  predicate isClient(DataFlowNode nd) {
    nd.getALocalSource() = newClient()
    or
    // pool.connect(function(err, client) { ... })
    exists (DataFlowNode pool, MethodCallExpr getConn, Function cb |
      isPool(pool) and getConn.calls(pool, "connect") and
      cb = getConn.getArgument(0).(DataFlowNode).getALocalSource() and
      nd.getALocalSource() = cb.getParameter(1).(SimpleParameter).getVariable().getAnAccess()
    )
  }

  /** Gets an expression that constructs a new connection pool. */
  NewExpr newPool() {
    // new require('pg').Pool()
    exists (ModuleInstance pg, PropReadNode pgPool |
      pg.getPath() = "pg" and
      pgPool.getBase().getALocalSource() = pg and pgPool.getPropertyName() = "Pool" and
      result.getCallee().(DataFlowNode).getALocalSource() = pgPool
    )
    or
    // new require('pg-pool')
    exists (ModuleInstance pgPool |
      pgPool.getPath() = "pg-pool" and
      result.getCallee().(DataFlowNode).getALocalSource() = pgPool
    )
  }

  /** Holds if `nd` may contain a Postgres pool instance. */
  predicate isPool(DataFlowNode nd) {
    nd.getALocalSource() = newPool()
  }

  /** An expression that is passed to the `query` method and hence interpreted as SQL. */
  class QueryString extends SQL::SqlString {
    QueryString() {
      exists (DataFlowNode base, MethodCallExpr mce |
        isClient(base) or isPool(base) |
        mce.calls(base, "query") and this = mce.getArgument(0)
      )
    }
  }

  /** An expression that is passed as user name or password when creating a client or a pool. */
  class Credentials extends CredentialsExpr {
    string kind;

    Credentials() {
      exists (NewExpr call, string prop |
        (call = newClient() or call = newPool())
        and
        call.hasOptionArgument(0, prop, this)
        and
        (
          prop = "user" and kind = "user name" or
          prop = "password" and kind = prop
        )
      )
    }

    override string getCredentialsKind() {
      result = kind
    }
  }
}

/**
 * Provides classes modelling the `sqlite3` package.
 */
private module Sqlite {
  /** Holds if `nd` may contain a reference to the `sqlite3` module. */
  predicate isSqlite(DataFlowNode nd) {
    nd.getALocalSource().(ModuleInstance).getPath() = "sqlite3"
    or
    exists (DataFlowNode sqlite | isSqlite(sqlite) |
      nd.getALocalSource().(MethodCallExpr).calls(sqlite, "verbose")
    )
  }

  /** Holds if `nd` may contain a Sqlite database instance. */
  predicate isDB(DataFlowNode nd) {
    // new require('sqlite3').Database()
    exists (PropReadNode db |
      isSqlite(db.getBase()) and db.getPropertyName() = "Database" and
      nd.getALocalSource().(NewExpr).getCallee().(DataFlowNode).getALocalSource() = db
    )
  }

  /** An expression that is passed to a method that interprets it as SQL. */
  class QueryString extends SQL::SqlString {
    QueryString() {
      exists (DataFlowNode base, MethodCallExpr mce, string meth |
        meth = "all" or meth = "each" or meth = "exec" or meth = "get" or meth = "prepare" or meth = "run" |
        isDB(base) and mce.calls(base, meth) and this = mce.getArgument(0)
      )
    }
  }
}

/**
 * Provides classes modelling the `mssql` package.
 */
private module MsSql {
  /** Holds if `nd` may contain a reference to the `mssql` module. */
  predicate isMsSql(DataFlowNode nd) {
    nd.getALocalSource().(ModuleInstance).getPath() = "mssql"
  }

  /** Holds if `nd` may contain a request object. */
  predicate isRequest(DataFlowNode nd) {
    // new require('mssql').Request()
    exists (PropReadNode db |
      isMsSql(db.getBase()) and db.getPropertyName() = "Request" and
      nd.getALocalSource().(NewExpr).getCallee().(DataFlowNode).getALocalSource() = db
    ) or
    // request.input(...)
    exists (DataFlowNode req | isRequest(req) |
      nd.getALocalSource().(MethodCallExpr).calls(req, "input")
    )
  }

  /** Holds if `e` is part of a tagged template evaluated as a query. */
  predicate isQueryTemplateElement(Expr e) {
    exists (DataFlowNode mssql, PropAccess query, TaggedTemplateExpr call |
      isMsSql(mssql) and query.accesses(mssql, "query") and
      call.getTag().(DataFlowNode).getALocalSource() = query and
      e = call.getTemplate().getAnElement()
    )
  }

  /** An expression that is passed to a method that interprets it as SQL. */
  class QueryString extends SQL::SqlString {
    QueryString() {
      isQueryTemplateElement(this) or
      exists (DataFlowNode base, MethodCallExpr query, string meth |
        meth = "query" or meth = "batch" |
        isRequest(base) and query.calls(base, meth) and
        this = query.getArgument(0)
      )
    }
  }

  /** An element of a query template, which is automatically sanitized. */
  class QueryTemplateSanitizer extends SQL::SqlSanitizer {
    QueryTemplateSanitizer() {
      isQueryTemplateElement(this) and
      input = this and output = this
    }
  }

  /** An expression that is passed as user name or password when creating a client or a pool. */
  class Credentials extends CredentialsExpr {
    string kind;

    Credentials() {
      exists (DataFlowNode mssql, InvokeExpr call, string prop |
        isMsSql(mssql)
        and
        (
         call.(MethodCallExpr).calls(mssql, "connect")
         or
         call.(NewExpr).getCallee().(PropAccess).accesses(mssql, "ConnectionPool")
        )
        and
        call.hasOptionArgument(0, prop, this)
        and
        (
          prop = "user" and kind = "user name" or
          prop = "password" and kind = prop
        )
      )
    }

    override string getCredentialsKind() {
      result = kind
    }
  }
}

/**
 * Provides classes modelling the `sequelize` package.
 */
private module Sequelize {
  /** Holds if `nd` may contain a reference to the `sequelize` module. */
  predicate isSequelize(DataFlowNode nd) {
    nd.getALocalSource().(ModuleInstance).getPath() = "sequelize"
  }

  /** Gets an expression that creates an instance of the `Sequelize` class. */
  NewExpr newSequelize() {
    isSequelize(result.getCallee())
  }

  /** Holds if `nd` may contain an instance of the `Sequelize` class. */
  predicate isSequelizeInstance(DataFlowNode nd) {
    nd.getALocalSource() = newSequelize()
  }

  /** An expression that is passed as the first argument to `Sequelize.query`. */
  class QueryString extends SQL::SqlString {
    QueryString() {
      exists (MethodCallExpr mce |
        isSequelizeInstance(mce.getReceiver()) and
        mce.getMethodName() = "query" and
        this = mce.getArgument(0)
      )
    }
  }

  /**
   * An expression that is passed as user name or password when creating an instance of the
   * `Sequelize` class.
   */
  class Credentials extends CredentialsExpr {
    string kind;

    Credentials() {
      exists (NewExpr ne, string prop |
        ne = newSequelize()
        and
        (
         this = ne.getArgument(1) and prop = "username"
         or
         this = ne.getArgument(2) and prop = "password"
         or
         ne.hasOptionArgument(ne.getNumArgument()-1, prop, this)
        )
        and
        (
         prop = "username" and kind = "user name"
         or
         prop = "password" and kind = prop
        )
      )
    }

    override string getCredentialsKind() {
      result = kind
    }
  }
}
