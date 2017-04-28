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
 * @name Comparison of identical values
 * @description If the same expression occurs on both sides of a comparison
 *              operator, the operator is redundant, and probably indicates a mistake.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       readability
 *       convention
 *       external/cwe/cwe-570
 *       external/cwe/cwe-571
 * @precision high
 */

import Clones

/**
 * Holds if `e` is a reference to variable `v`, possibly with parentheses or
 * numeric conversions (that is, the unary operators `+` or `-` or a call to `Number`)
 * applied.
 */
predicate accessWithConversions(Expr e, Variable v) {
  e = v.getAnAccess()
  or
  accessWithConversions(e.(ParExpr).getExpression(), v)
  or
  exists (UnaryExpr ue | ue instanceof NegExpr or ue instanceof PlusExpr |
    ue = e and accessWithConversions(ue.getOperand(), v)
  ) or
  exists (CallExpr ce | ce = e |
    ce.getCallee().(GlobalVarAccess).getName() = "Number" and
    ce.getNumArgument() = 1 and
    accessWithConversions(ce.getArgument(0), v)
  )
}

/**
 * Holds if the equality test `eq` looks like a NaN check.
 *
 * In order to qualify as a NaN check, both sides of the equality have
 * to be references to the same variable `x`, possibly with added parentheses
 * or numeric conversions, and one of the following holds:
 *
 *   - `x` is a parameter of the enclosing function, which is called
 *     `isNaN` (modulo capitalization);
 *   - there is a comment next to the comparison (that is, no further than
 *     one line away in either direction) that contains the word `NaN`.
 */
predicate isNaNCheck(EqualityTest eq) {
  exists (Variable v |
    accessWithConversions(eq.getLeftOperand(), v) and
    accessWithConversions(eq.getRightOperand(), v) |

    // `v` is a parameter of the enclosing function, which is called `isNaN`
    exists (Function isNaN |
      isNaN = eq.getEnclosingFunction() and
      isNaN.getName().toLowerCase() = "isnan" and
      v = isNaN.getAParameter().getAVariable()
    ) or

    // there is a comment containing the word "NaN" next to the comparison
    exists (int eqLine, Comment c |
      eqLine = eq.getLocation().getStartLine() and
      c.getFile() = eq.getFile() and
      c.getLocation().getStartLine() in [eqLine-1..eqLine+1] and
      c.getText().matches("%NaN%")
    )
  )
}

from Comparison selfComparison, OperandComparedToSelf e
where e = selfComparison.getAnOperand() and e.same(_) and
      not isNaNCheck(selfComparison)
select selfComparison, "This expression compares $@ to itself.", e, e.toString()
