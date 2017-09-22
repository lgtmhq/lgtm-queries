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
 * Provides classes and predicates implementing the UnsignedGEZero query.
 * This library is also used by the PointlessComparison query,
 * so that we can avoid reporting the same result twice. (PointlessComparison
 * is a newer and more general query which also finds instances of
 * the UnsignedGEZero pattern.)
 */

import cpp

class ConstantZero extends Expr {
  ConstantZero() {
    this.isConstant() and
    this.getValue() = "0"
  }
}

class UnsignedGEZero extends GEExpr {
  UnsignedGEZero() {
    this.getRightOperand() instanceof ConstantZero and

    // left operand was a signed or unsigned IntegralType before conversions
    // (not a pointer, checking a pointer >= 0 is an entirely different mistake)
    // (not an enum, as the fully converted type of an enum is compiler dependent
    //  so checking an enum >= 0 is always reasonable)
    getLeftOperand().getUnderlyingType() instanceof IntegralType and

    exists(Expr ue |
      // ue is some conversion of the left operand
      ue = getLeftOperand().getConversion*() and

      // ue is unsigned
      ue.getUnderlyingType().(IntegralType).isUnsigned() and

      // ue may be converted to zero or more strictly larger possibly signed types
      // before it is fully converted
      forall(Expr following | following = ue.getConversion+() |
        following.getType().getSize() > ue.getType().getSize()
      )
    )
  }
}

predicate unsignedGEZero(UnsignedGEZero ugez, string msg) {
  not exists(MacroInvocation mi |
    // ugez is in mi
    mi.getAnExpandedElement() = ugez and

    // and ugez was apparently not passed in as a macro parameter
    mi.getLocation().toString() = ugez.getLocation().toString()
  ) and
  msg = "Pointless comparison of unsigned value to zero."
}
