// Copyright 2016 Semmle Ltd.
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
 * @name User-controlled data in numeric cast
 * @description Casting user-controlled numeric data to a narrower type without validation
 *              can cause unexpected truncation.
 * @kind problem
 * @problem.severity warning
 * @cwe 197 681
 */
import default
import semmle.code.java.security.DataFlow
import NumericCastCommon

from NumericNarrowingCastExpr exp, VarAccess tainted, RemoteUserInput origin
where
  exp.getExpr() = tainted and
  origin.flowsTo(tainted)
  and not exists(ConditionalStmt c, ComparisonExpr guard |
    priorAccess(tainted) = guard.getAnOperand() and
    guard = c.getCondition().getAChildExpr*() and
    dominates(c, exp.getEnclosingStmt())
  )
  and not exists(RightShiftOp e | e.getShiftedVariable() = tainted.getVariable())
  and not exp.getEnclosingCallable() instanceof HashCodeMethod
select exp, "$@ flows to here and is cast to a narrower type, potentially causing truncation.",
  origin, "User-provided value"
