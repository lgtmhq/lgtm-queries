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

/* Definitions used by the SQL injection queries. */

import semmle.code.java.Expr
import semmle.code.java.security.DataFlow

class SqlInjectionSink extends Expr {
  SqlInjectionSink() {
    this instanceof SqlExpr or
    exists(SQLiteRunner s, MethodAccess m | m.getMethod() = s |
      m.getArgument(s.sqlIndex()) = this
    )
  }
}

/**
 * Implementation of `SqlTainted.ql`. This is extracted to a QLL so that it
 * can be excluded from `SqlUnescaped.ql` to avoid overlapping results.
 */
predicate queryTaintedBy(SqlInjectionSink query, UserInput source) {
  source.flowsTo(query)
}
