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
 * @name Useless assignment to local variable
 * @description An assignment to a local variable that is not used later on, or whose value is always
 *              overwritten, has no effect.
 * @kind problem
 * @problem.severity warning
 */

import javascript

predicate deadStoreOfLocal(VarDef vd, PurelyLocalVariable v) {
  v = vd.getAVariable() and
  exists (vd.getSource()) and
  not localDefinitionReaches(v, vd, _)
}

predicate isNullOrUndef(Expr e) {
  // `null` or `undefined`
  e instanceof NullLiteral or e.(VarAccess).getName() = "undefined" or
  // recursive case to catch multi-assignments of the form `x = y = null`
  isNullOrUndef(e.(AssignExpr).getRhs())
}

predicate isDefaultInit(Expr e) {
  // primitive default values: zero, false, empty string, and (integer) -1
  e.(NumberLiteral).getValue().toFloat() = 0.0 or
  e.(NegExpr).getOperand().(NumberLiteral).getValue() = "1" or
  e.(StringLiteral).getValue() = "" or
  e.(BooleanLiteral).getValue() = "false" or
  // recursive case
  isDefaultInit(e.(AssignExpr).getRhs())
}

from VarDef dead, PurelyLocalVariable v  // captured variables may be read by closures, so don't flag them
where deadStoreOfLocal(dead, v) and
      // the variable should be accessed somewhere; otherwise it will be flagged by UnusedVariable
      exists(v.getAnAccess()) and
      // don't flag function expressions
      not exists (FunctionExpr fe | dead = fe.getId()) and
      // don't flag overwrites with `null` or `undefined`
      not isNullOrUndef(dead.getSource()) and
      // don't flag default inits that are later overwritten
      not (isDefaultInit(dead.getSource()) and localDefinitionOverwrites(v, dead, _))
select dead, "This statement assigns a value to " + v.getName() + " that is never read."
