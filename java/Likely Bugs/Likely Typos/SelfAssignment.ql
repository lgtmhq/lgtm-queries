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
 * @name Self assignment
 * @description Assigning a variable to itself has no effect.
 * @kind problem
 * @problem.severity error
 */

import java

predicate toCompare(VarAccess left, VarAccess right) {
  exists(AssignExpr assign | assign.getDest() = left and assign.getSource() = right)
  or
  exists(VarAccess outerleft, VarAccess outerright |
    toCompare(outerleft, outerright) and
    left = outerleft.getQualifier() and
    right = outerright.getQualifier()
  )
}

predicate local(RefType enclosingType, VarAccess v) {
  enclosingType = v.getQualifier().(ThisAccess).getType() or
  not exists(v.getQualifier()) and enclosingType = v.getEnclosingCallable().getDeclaringType()
}

predicate sameVariable(VarAccess left, VarAccess right) {
  toCompare(left, right) and
  left.getVariable() = right.getVariable() and
  (
    exists (Expr q1, Expr q2 |
      q1 = left.getQualifier() and
      sameVariable(q1, q2) and
      q2 = right.getQualifier()
    ) or
    exists (RefType enclosingType |
      local(enclosingType, left) and local(enclosingType, right)
    )
  )
}

from AssignExpr assign
where sameVariable(assign.getDest(), assign.getSource())
select assign,
  "This assigns the variable " + assign.getDest().(VarAccess).getVariable().getName() +
  " to itself and has no effect."
