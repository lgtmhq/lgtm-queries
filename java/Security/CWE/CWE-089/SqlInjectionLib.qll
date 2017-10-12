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

/** Definitions used by the queries for database query injection. */

import semmle.code.java.Expr
import semmle.code.java.security.DataFlow
import semmle.code.java.frameworks.javaee.Persistence

/** A sink for database query language injection vulnerabilities. */
abstract class QueryInjectionSink extends Expr {}

/** A sink for SQL injection vulnerabilities. */
class SqlInjectionSink extends QueryInjectionSink {
  SqlInjectionSink() {
    this instanceof SqlExpr or
    exists(SQLiteRunner s, MethodAccess m | m.getMethod() = s |
      m.getArgument(s.sqlIndex()) = this
    )
  }
}

/** A sink for Java Persistence Query Language injection vulnerabilities. */
class PersistenceQueryInjectionSink extends QueryInjectionSink {
  PersistenceQueryInjectionSink() {
    // the query (first) argument to a `createQuery` or `createNativeQuery` method on `EntityManager`
    exists (MethodAccess call, TypeEntityManager em | call.getArgument(0) = this |
      call.getMethod() = em.getACreateQueryMethod() or
      call.getMethod() = em.getACreateNativeQueryMethod()
      // note: `createNamedQuery` is safe, as it takes only the query name,
      // and named queries can only be constructed using constants as the query text 
    )
  }
}


/**
 * Implementation of `SqlTainted.ql`. This is extracted to a QLL so that it
 * can be excluded from `SqlUnescaped.ql` to avoid overlapping results.
 */
predicate queryTaintedBy(QueryInjectionSink query, UserInput source) {
  source.flowsTo(query)
}
