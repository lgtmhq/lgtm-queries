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
 * @name SQL query built without neutralizing special characters
 * @description Building a SQL query without escaping or otherwise neutralizing any special
 *              characters is vulnerable to insertion of malicious SQL code.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @tags security
 *       external/cwe/cwe-089
 */

import semmle.code.java.security.SqlUnescapedLib
import SqlInjectionLib

class UncontrolledStringBuilderSource extends FlowSource {
  UncontrolledStringBuilderSource() {
    exists(StringBuilderVar sbv | 
      uncontrolledStringBuilderQuery(sbv, _) and
      this = sbv.getToStringCall()
    )
  }
}

from SqlInjectionSink query, Expr uncontrolled
where
  (
    builtFromUncontrolledConcat(query, uncontrolled) or
    exists (StringBuilderVar sbv |
      uncontrolledStringBuilderQuery(sbv, uncontrolled) and
      sbv.getToStringCall().(UncontrolledStringBuilderSource).flowsTo(query)
    )
  )
  and not queryTaintedBy(query, _)
select
  query, "Query might not neutralize special characters in $@.",
  uncontrolled, "this expression"
