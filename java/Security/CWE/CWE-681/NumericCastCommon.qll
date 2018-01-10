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

import java
import semmle.code.java.arithmetic.Overflow
import semmle.code.java.dataflow.SSA
import semmle.code.java.dataflow.Guards

class NumericNarrowingCastExpr extends CastExpr {
  NumericNarrowingCastExpr() {
    exists(NumericType sourceType, NumericType targetType |
      sourceType = getExpr().getType() and targetType = getType() |
      not targetType.(NumType).widerThanOrEqualTo(sourceType.(NumType))
    )
  }
}

class RightShiftOp extends Expr {
  RightShiftOp() {
    this instanceof RShiftExpr or
    this instanceof URShiftExpr or
    this instanceof AssignRShiftExpr or
    this instanceof AssignURShiftExpr
  }

  private Expr getLhs() {
    this.(BinaryExpr).getLeftOperand() = result or
    this.(Assignment).getDest() = result
  }

  Variable getShiftedVariable() {
    getLhs() = result.getAnAccess() or
    getLhs().getProperExpr().(AndBitwiseExpr).getAnOperand() = result.getAnAccess()
  }
}

predicate boundedRead(RValue read) {
  exists(SsaVariable v, ConditionBlock cb, ComparisonExpr comp, boolean testIsTrue |
    read = v.getAUse() and
    cb.controls(read.getBasicBlock(), testIsTrue) and
    cb.getCondition() = comp
    |
    comp.getLesserOperand() = v.getAUse() and testIsTrue = true or
    comp.getGreaterOperand() = v.getAUse() and testIsTrue = false
  )
}

predicate castCheck(RValue read) {
  exists(EqualityTest eq, CastExpr cast |
    cast.getExpr() = read and
    eq.hasOperands(cast, read.getVariable().getAnAccess())
  )
}
