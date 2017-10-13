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
 * @name Uncontrolled data in SQL query
 * @description Including user-supplied data in a SQL query without
 *              neutralizing special elements can make code vulnerable
 *              to SQL Injection.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 */
import cpp
import semmle.code.cpp.security.Security
import semmle.code.cpp.security.FunctionWithWrappers
import semmle.code.cpp.security.TaintTracking

class SQLLikeFunction extends FunctionWithWrappers {
  SQLLikeFunction() {
    sqlArgument(this.getName(), _)
  }

  predicate interestingArg(int arg) {
    sqlArgument(this.getName(), arg)
  }
}

from SQLLikeFunction runSql,
     Expr taintedArg, Expr taintSource, string taintCause, string callChain
where runSql.outermostWrapperFunctionCall(taintedArg, callChain)
  and tainted(taintSource, taintedArg)
  and isUserInput(taintSource, taintCause)
select
  taintedArg,
  "This argument to a SQL query function is derived from $@ and then passed to " + callChain,
  taintSource, "user input (" + taintCause + ")"
