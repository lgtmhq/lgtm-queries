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
 * @name SQL query built from user-controlled sources
 * @description Building a SQL query from user-controlled sources is vulnerable to insertion of
 *              malicious SQL code by the user.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 */

import semmle.code.java.Expr
import semmle.code.java.security.DataFlow
import SqlInjectionLib


from SqlInjectionSink query, RemoteUserInput source
where queryTaintedBy(query, source)
select query, "Query might include code from $@.",
  source, "this user input"
