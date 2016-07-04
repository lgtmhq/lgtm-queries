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
 * @name Useless type test
 * @description Comparing the result of a typeof test against a string other than 'undefined',
 *              'boolean', 'number', 'string', 'object', 'function' or 'symbol' is useless, since
 *              this comparison can never succeed.
 * @kind problem
 * @problem.severity error
 */

import default

/**
 * Common abstraction for equality tests and switch cases. Switch
 * statements are recast as equality tests between the discriminant
 * and the case expressions. 
 */
class EqOrSwitch extends ASTNode {
  EqOrSwitch() {
    this instanceof EqualityTest or
    this instanceof Case
  }

  Expr getAnOperand() {
    result = ((EqualityTest)this).getAnOperand() or
    exists (Case c | c = this |
      result = c.getSwitch().getExpr() or
      result = c.getExpr()
    )
  }
}

from EqOrSwitch et, TypeofExpr typeof, StringLiteral str
where typeof = et.getAnOperand().stripParens() and
      str = et.getAnOperand().stripParens() and
      not str.getValue().regexpMatch("undefined|boolean|number|string|object|function|symbol|unknown|date")
select typeof, "The result of this 'typeof' expression is compared to $@, but the two can never be equal.", str, str.toString()
