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
 * @name Query built without neutralizing special characters
 * @description Building a SQL or Java Persistence query without escaping or otherwise neutralizing any special
 *              characters is vulnerable to insertion of malicious code.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/concatenated-sql-query
 * @tags security
 *       external/cwe/cwe-089
 */

import semmle.code.java.security.SqlUnescapedLib
import SqlInjectionLib

class UncontrolledStringBuilderSource extends DataFlow::ExprNode {
  UncontrolledStringBuilderSource() {
    exists(StringBuilderVar sbv | 
      uncontrolledStringBuilderQuery(sbv, _) and
      this.getExpr() = sbv.getToStringCall()
    )
  }
}

class UncontrolledStringBuilderSourceFlowConfig extends TaintTracking::Configuration {
  UncontrolledStringBuilderSourceFlowConfig() { this = "SqlUnescaped::UncontrolledStringBuilderSourceFlowConfig" }
  override predicate isSource(DataFlow::Node src) { src instanceof UncontrolledStringBuilderSource }
  override predicate isSink(DataFlow::Node sink) { sink instanceof QueryInjectionSink }
}

from QueryInjectionSink query, Expr uncontrolled
where
  (
    builtFromUncontrolledConcat(query.getExpr(), uncontrolled) or
    exists (StringBuilderVar sbv, UncontrolledStringBuilderSourceFlowConfig conf |
      uncontrolledStringBuilderQuery(sbv, uncontrolled) and
      conf.hasFlow(DataFlow::exprNode(sbv.getToStringCall()), query)
    )
  )
  and not queryTaintedBy(query, _)
select
  query, "Query might not neutralize special characters in $@.",
  uncontrolled, "this expression"
