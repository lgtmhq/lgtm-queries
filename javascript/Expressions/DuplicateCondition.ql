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
 * @name Duplicate 'if' condition
 * @description If two conditions in an 'if'-'else if' chain are identical, the
 *              second condition will never be evaluated.
 * @kind problem
 * @problem.severity error
 * @tags maintainability
 *       correctness
 * @precision very-high
 */

import Clones

/** Gets the `i`th condition in the `if`-`else if` chain starting at `stmt`. */
Expr getCondition(IfStmt stmt, int i) {
  i = 0 and result = stmt.getCondition() or
  result = getCondition(stmt.getElse(), i-1)
}

/**
 * A detector for duplicated `if` conditions in the same `if`-`else if` chain.
 */
class DuplicateIfCondition extends StructurallyCompared {
  DuplicateIfCondition() {
    this = getCondition(_, 0)
  }

  override Expr candidate() {
    exists (IfStmt stmt, int j | this = getCondition(stmt, 0) |
      j > 0 and result = getCondition(stmt, j)
    )
  }
}

from DuplicateIfCondition e, Expr f
where e.same(f)
select f, "This condition is a duplicate of $@.", e, e.toString()