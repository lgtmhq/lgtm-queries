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
 * @name Implicit narrowing conversion in compound assignment
 * @description Compound assignment statements (for example 'intvar += longvar') that implicitly 
 *              cast a value of a wider type to a narrower type may result in information loss and 
 *              numeric errors such as overflows.
 * @kind problem
 * @problem.severity warning
 * @cwe 190 192 197 681
 */
import semmle.code.java.arithmetic.Overflow

class DangerousAssignOpExpr extends AssignOp {
  DangerousAssignOpExpr() {
    this instanceof AssignAddExpr or
    this instanceof AssignMulExpr
  }
}

predicate problematicCasting(Type t, Expr e) {
  e.getType().(NumType).widerThan((NumType)t)
}

from DangerousAssignOpExpr a, Expr e
where
  e = a.getSource() and
  problematicCasting(a.getDest().getType(), e)
select a,
  "Implicit cast of source type " + e.getType().getName() +
  " to narrower destination type " + a.getDest().getType().getName() + "."
