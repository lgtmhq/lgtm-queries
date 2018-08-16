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
 * @name User-controlled data in arithmetic expression
 * @description Arithmetic operations on user-controlled data that is not validated can cause
 *              overflows.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/tainted-arithmetic
 * @tags security
 *       external/cwe/cwe-190
 *       external/cwe/cwe-191
 */
import java
import semmle.code.java.dataflow.FlowSources
import ArithmeticCommon

predicate sink(ArithExpr exp, VarAccess tainted, string effect) {
  exp.getAnOperand() = tainted and
  (
    (not guardedAgainstUnderflow(exp, tainted) and effect = "underflow") or 
    (not guardedAgainstOverflow(exp, tainted) and effect = "overflow")
  )
  // Exclude widening conversions of tainted values due to binary numeric promotion (JLS 5.6.2)
  // unless there is an enclosing cast down to a narrower type.
  and narrowerThanOrEqualTo(exp, tainted.getType())
  and not overflowIrrelevant(exp)
}

class RemoteUserInputConfig extends TaintTracking::Configuration {
  RemoteUserInputConfig() { this = "ArithmeticTainted.ql:RemoteUserInputConfig" }
  override predicate isSource(DataFlow::Node source) { source instanceof RemoteUserInput }
  override predicate isSink(DataFlow::Node sink) { sink(_, sink.asExpr(), _) }
  override predicate isSanitizer(DataFlow::Node n) { n.getType() instanceof BooleanType }
}

from ArithExpr exp, VarAccess tainted, RemoteUserInput origin, string effect, RemoteUserInputConfig conf
where
  conf.hasFlow(origin, DataFlow::exprNode(tainted)) and
  sink(exp, tainted, effect)
select exp, "$@ flows to here and is used in arithmetic, potentially causing an " + effect + ".", 
  origin, "User-provided value"
