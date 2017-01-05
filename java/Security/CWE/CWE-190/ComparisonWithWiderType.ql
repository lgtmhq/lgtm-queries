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
 * @name Comparison of narrow type with wide type in loop condition
 * @description Comparisons between types of different widths in a loop condition can cause the loop
 *              to behave unexpectedly.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       security
 *       external/cwe/cwe-190
 *       external/cwe/cwe-197
 */
import java
import semmle.code.java.arithmetic.Overflow

int leftWidth(ComparisonExpr e) {
  result = e.getLeftOperand().getType().(NumType).getWidthRank()
}

int rightWidth(ComparisonExpr e) {
  result = e.getRightOperand().getType().(NumType).getWidthRank()
}

abstract class WideningComparison extends BinaryExpr {
  WideningComparison() {
    this instanceof ComparisonExpr
  }
  abstract Expr getNarrower();
  abstract Expr getWider();
}

class LTWideningComparison extends WideningComparison {
  LTWideningComparison() {
    (this instanceof LEExpr or this instanceof LTExpr) and
    leftWidth(this) < rightWidth(this)
  }
  
  Expr getNarrower() {
    result = getLeftOperand()
  }
  
  Expr getWider() {
    result = getRightOperand()
  }
}

class GTWideningComparison extends WideningComparison {
  GTWideningComparison() {
    (this instanceof GEExpr or this instanceof GTExpr) and
    leftWidth(this) > rightWidth(this)
  }
  
  Expr getNarrower() {
    result = getRightOperand()
  }
  
  Expr getWider() {
    result = getLeftOperand()
  }
}

from WideningComparison c, LoopStmt l
where 
  not c.getAnOperand().isCompileTimeConstant()
  and l.getCondition().getAChildExpr*() = c
select c, "Comparison between $@ of type " + c.getNarrower().getType().getName() +
  " and $@ of wider type " + c.getWider().getType().getName() + ".",
  c.getNarrower(), "expression",
  c.getWider(), "expression"
