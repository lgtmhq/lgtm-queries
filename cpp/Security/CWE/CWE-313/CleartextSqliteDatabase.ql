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
 * @name Cleartext storage of sensitive information in an SQLite database
 * @description Storing sensitive information in a non-encrypted
 *              database can expose it to an attacker.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/cleartext-storage-database
 * @tags security
 *       external/cwe/cwe-313
 */

import cpp
import semmle.code.cpp.security.SensitiveExprs
import semmle.code.cpp.security.TaintTracking

class UserInputIsSensitiveExpr extends SecurityOptions {
  predicate isUserInput(Expr expr, string cause) {
    expr instanceof SensitiveExpr and cause = "sensitive information"
  }
}

class SqliteFunctionCall extends FunctionCall {
  SqliteFunctionCall() {
    this.getTarget().getName().matches("sqlite%")
  }

  Expr getASource() {
    result = this.getAnArgument()
  }
}

predicate sqlite_encryption_used() {
  any(StringLiteral l).getValue().toLowerCase().regexpMatch("pragma key.*") or
  any(StringLiteral l).getValue().toLowerCase().matches("%attach%database%key%") or
  any(FunctionCall fc).getTarget().getName().matches("sqlite%\\_key\\_%")
}

from SensitiveExpr taintSource, Expr taintedArg, SqliteFunctionCall sqliteCall
where tainted(taintSource, taintedArg)
  and taintedArg = sqliteCall.getASource()
  and not sqlite_encryption_used()
select sqliteCall, "This SQLite call may store $@ in a non-encrypted SQLite database",
       taintSource, "sensitive information"

