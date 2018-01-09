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
* @name Database query built from user-controlled sources
* @description Building a database query from user-controlled sources is vulnerable to insertion of
*              malicious code by the user.
* @kind problem
* @problem.severity error
* @precision high
* @id js/sql-injection
* @tags security
*       external/cwe/cwe-089
*/

import javascript
import semmle.javascript.security.dataflow.SqlInjection
import semmle.javascript.security.dataflow.NosqlInjection

from DataFlowNode source, DataFlowNode sink
where any(SqlInjectionTrackingConfig cfg).flowsFrom(sink, source) or
      any(NosqlInjectionTrackingConfig cfg).flowsFrom(sink, source)
select sink, "This query depends on $@.", source, "a user-provided value"
