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
 * @name Inconsistent direction of for loop
 * @description A 'for' loop that increments its loop variable but checks it
 *              against a lower bound, or decrements its loop variable but
 *              checks it against an upper bound, will either stop iterating
 *              immediately or keep iterating indefinitely, and is usually
 *              indicative of a typo.
 * @kind problem
 * @problem.severity error
 * @tags correctness
 * @precision very-high
 */

import javascript

/**
 * Holds if `test` bounds `v` in `direction`, which is either `"upward"`
 * or `"downward"`.
 *
 * For example, `x < 42` bounds `x` upward, while `y >= 0` bounds `y`
 * downward.
 */
predicate bounds(RelationalComparison test, Variable v, string direction) {
  test.getLesserOperand() = v.getAnAccess() and direction = "upward" or
  test.getGreaterOperand() = v.getAnAccess() and direction = "downward"
}

/**
 * Holds if `upd` updates `v` in `direction`, which is either `"upward"`
 * or `"downward"`.
 *
 * For example, `++x` updates `x` upward, while `y--` updates `y`
 * downward.
 */
predicate updates(UpdateExpr upd, Variable v, string direction) {
  upd.getOperand() = v.getAnAccess() and
  (upd instanceof IncExpr and direction = "upward" or
   upd instanceof DecExpr and direction = "downward")
}

from ForStmt l, Variable v, string d1, string d2
where bounds(l.getTest(), v, d1) and
      updates(l.getUpdate(), v, d2) and
      d1 != d2
select l, "This loop counts " + d2 + ", but its variable is bounded " + d1 + "."
