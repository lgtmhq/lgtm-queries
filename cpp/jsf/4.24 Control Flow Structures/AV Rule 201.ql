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
 * @name For loop variable changed in body
 * @description Numeric variables being used within a for loop for iteration counting should not be modified in the body of the loop. Reserve for loops for straightforward iterations, and use a while loop instead for more complex cases.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/loop-variable-changed
 * @tags reliability
 *       readability
 */
import cpp
import Likely_Bugs.NestedLoopSameVar

pragma[noopt]
predicate loopModification(ForStmt for, Variable loopVariable, VariableAccess acc) {
  loopVariable = for.getAnIterationVariable() and
  acc = loopVariable.getAnAccess() and
  acc.isModified() and
  exists(Stmt stmt | acc.getEnclosingStmt() = stmt and stmtInForBody(stmt, for))
}

pragma[noopt]
predicate stmtInForBody(Stmt stmt, ForStmt forStmt) {
  forStmt.getStmt() = stmt or exists(StmtParent parent | parent = stmt.getParent() | stmtInForBody(parent, forStmt))
}

from ForStmt for, Variable loopVariable, VariableAccess acc
where
  loopModification(for, loopVariable, acc) and

  // don't duplicate results from NestedLoopSameVar.ql
  not exists(ForStmt inner |
    nestedForViolation(inner, loopVariable, for) and
    (
      acc.getParent*() = inner or
      acc.getParent*() = inner.getInitialization()
    )
  )
select
  acc, "Loop counters should not be modified in the body of the $@.",
  for.getStmt(), "loop"
