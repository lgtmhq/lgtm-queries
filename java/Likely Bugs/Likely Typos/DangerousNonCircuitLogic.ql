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
 * @name Dangerous non-short-circuit logic
 * @description Using a bitwise logical operator on a Boolean where a conditional-and or
 *              conditional-or operator is intended is likely to give the wrong result and may
 *              cause an exception.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @tags reliability
 *       readability
 *       external/cwe/cwe-691
 */
import java

/** An expression containing a method access, array access, or qualified field access. */
class DangerousExpression extends Expr {
  DangerousExpression() {
    exists(Expr e | this = e.getParent*() |
      e instanceof MethodAccess or
      e instanceof ArrayAccess or
      exists(e.(FieldAccess).getQualifier())
    )
  }
}

/** A use of `&` or `|` on operands of type boolean. */
class NonShortCircuit extends BinaryExpr {
  NonShortCircuit() {
    (   this instanceof AndBitwiseExpr
     or this instanceof OrBitwiseExpr) and
    this.getLeftOperand().getType().hasName("boolean") and
    this.getRightOperand().getType().hasName("boolean") and
    this.getRightOperand() instanceof DangerousExpression
  }
}

from NonShortCircuit e
select e, "Possibly dangerous use of non-short circuit logic."
