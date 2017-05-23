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
import semmle.code.java.arithmetic.Overflow
import semmle.code.java.dataflow.DefUse

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

  Variable getShiftedVariable() {
    this.(BinaryExpr).getLeftOperand() = result.getAnAccess() or
    this.(Assignment).getDest() = result.getAnAccess()
  }
}

VarAccess priorAccess(VarAccess access) {
  useUsePair(result, access)
}
