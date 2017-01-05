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

import java 

/**
 * If `e1` evaluates to `b1` then the direct subexpression `e2` evaluates to `b2`.
 *
 * Used as basis for the transitive closure in `exprImplies`.
 */
private predicate exprImpliesStep(Expr e1, boolean b1, Expr e2, boolean b2) {
  e1.(ParExpr).getProperExpr() = e2 and b2 = b1 and (b1 = true or b1 = false)
  or
  e1.(LogNotExpr).getExpr() = e2 and b2 = b1.booleanNot() and (b1 = true or b1 = false)
  or
  b1 = true and e1.(AndLogicalExpr).getAnOperand() = e2 and b2 = true
  or
  b1 = false and e1.(OrLogicalExpr).getAnOperand() = e2 and b2 = false
}

/** If `e1` evaluates to `b1` then the subexpression `e2` evaluates to `b2`. */
predicate exprImplies(Expr e1, boolean b1, Expr e2, boolean b2) {
  e1 = e2 and b1 = b2 and (b1 = true or b1 = false)
  or
  exists(Expr emid, boolean bmid | exprImplies(e1, b1, emid, bmid) and exprImpliesStep(emid, bmid, e2, b2))
}
