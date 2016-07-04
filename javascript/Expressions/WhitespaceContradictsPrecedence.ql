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
 * @name Whitespace contradicts operator precedence
 * @description Nested expressions where the formatting contradicts the grouping enforced by operator precedence
 *              are difficult to read and may even indicate a bug.
 * @kind problem
 * @problem.severity warning
 */

import default

/* A binary expression of the form x op y, which is itself an operand (say, the left) of
 * another binary expression (x op y) op' y' such that (x op y) op' y' = x op (y op' y),
 * disregarding overflow. */
class AssocNestedExpr extends BinaryExpr {
  AssocNestedExpr() {
    exists(BinaryExpr parent, int idx | this = parent.getChildExpr(idx) |
      // +, *, &&, || and the bitwise operations are associative
      ((this instanceof AddExpr or this instanceof MulExpr or
        this instanceof BitwiseExpr or this instanceof LogicalBinaryExpr) and
        parent.getOperator() = this.getOperator())
      or
      // (x*y)/z = x*(y/z)
      (this instanceof MulExpr and parent instanceof DivExpr and idx = 0)
      or
      // (x/y)%z = x/(y%z)
      (this instanceof DivExpr and parent instanceof ModExpr and idx = 0)
      or
      // (x+y)-z = x+(y-z)
      (this instanceof AddExpr and parent instanceof SubExpr and idx = 0))
  }
}

/* A binary expression nested inside another binary expression where the inner operator ``obviously''
 * binds tighter than the outer one. This is obviously subjective. */
class HarmlessNestedExpr extends BinaryExpr {
  HarmlessNestedExpr() {
    exists(BinaryExpr parent | this = parent.getAChildExpr() |
      (parent instanceof Comparison and (this instanceof ArithmeticExpr or this instanceof ShiftExpr))
      or
      (parent instanceof LogicalExpr and this instanceof Comparison))
  }
}

// two helper predicates to enforce good join order
predicate startOfBinaryRhs(BinaryExpr expr, int line, int col) {
  exists(Location rloc | rloc = expr.getRightOperand().getLocation() |
    rloc.getStartLine() = line and rloc.getStartColumn() = col
  )
}

predicate endOfBinaryLhs(BinaryExpr expr, int line, int col) {
  exists(Location lloc | lloc = expr.getLeftOperand().getLocation() |
    lloc.getEndLine() = line and lloc.getEndColumn() = col
  )
}

/* Compute whitespace around the operator. */
int operatorWS(BinaryExpr expr) {
  exists(int line, int lcol, int rcol |
    endOfBinaryLhs(expr, line, lcol) and
    startOfBinaryRhs(expr, line, rcol) and
    result = rcol - lcol + 1 - expr.getOperator().length()
  )
}

/* Find nested binary expressions where the programmer may have made a precedence mistake. */
predicate interestingNesting(BinaryExpr inner, BinaryExpr outer) {
  inner = outer.getAChildExpr() and
  not inner instanceof AssocNestedExpr and
  not inner instanceof HarmlessNestedExpr
}

from BinaryExpr inner, BinaryExpr outer, int wsouter, int wsinner
where interestingNesting(inner, outer) and
      wsinner = operatorWS(inner) and wsouter = operatorWS(outer) and
      wsinner % 2 = 0 and wsouter % 2 = 0 and
      wsinner > wsouter
select outer, "Whitespace around nested operators contradicts precedence."
