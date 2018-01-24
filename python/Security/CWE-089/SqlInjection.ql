// Copyright 2018 Semmle Ltd.
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
 * @precision medium
 * @id py/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 *       external/owasp/owasp-a1
 */

import python

/* Sources */
import semmle.python.web.HttpRequest

/* Sinks */
import semmle.python.security.injection.Sql
import semmle.python.web.django.Db


from TaintSource src, TaintSink sink
where src.flowsToSink(sink)

select sink, "This SQL query depends on $@.", src, "a user-provided value"
