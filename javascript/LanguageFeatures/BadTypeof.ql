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

/**
 * @name Useless type test
 * @description Comparing the result of a typeof test against a string other than 'undefined',
 *              'boolean', 'number', 'string', 'object', 'function' or 'symbol' is useless, since
 *              this comparison can never succeed.
 * @kind problem
 * @problem.severity error
 * @id js/useless-type-test
 * @tags maintainability
 *       correctness
 *       language-features
 *       external/cwe/cwe-570
 *       external/cwe/cwe-571
 * @precision very-high
 */

import javascript

/**
 * A comparison construct, that is, either an equality test or a switch case
 * (which is implicitly compared to the switch statement's discriminant).
 */
class EqOrSwitch extends ASTNode {
  EqOrSwitch() {
    this instanceof EqualityTest or
    this instanceof Case
  }

  /**
   * Gets an operand of this comparison.
   *
   * For equality tests, the result is one of the operands; for switch cases,
   * the result is either the case expression or the discriminant of the
   * switch statement.
   *
   * Thus, the operands of `x !== 0` are `x` and `0`, while the operands
   * of `case 1:` in `switch (y) { case 1: ... }` are `y` and `1`.
   */
  Expr getAnOperand() {
    result = ((EqualityTest)this).getAnOperand()
    or
    exists (Case c | c = this |
      result = c.getSwitch().getExpr() or
      result = c.getExpr()
    )
  }
}

from EqOrSwitch et, TypeofExpr typeof, ConstantString str
where typeof = et.getAnOperand().stripParens() and
      str = et.getAnOperand().stripParens() and
      not str.getStringValue().regexpMatch("undefined|boolean|number|string|object|function|symbol|unknown|date|bigint")
select typeof, "The result of this 'typeof' expression is compared to '$@', but the two can never be equal.", str, str.getStringValue()
