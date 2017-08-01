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
 * @name Nested loops with same variable
 * @description Nested loops in which the iteration variable is the same for each loop are difficult
 *              to understand.
 * @kind problem
 * @problem.severity warning
 * @id js/nested-loops-with-same-variable
 * @tags maintainability
 *       correctness
 * @precision medium
 */

import javascript

/**
 * Gets an iteration variable that loop `for` tests and updates.
 */
Variable getAnIterationVariable(ForStmt for) {
    result.getAnAccess().getParentExpr*() = for.getTest() and
    exists (UpdateExpr upd | upd.getParentExpr*() = for.getUpdate() | upd.getOperand() = result.getAnAccess())
}

from ForStmt outer, ForStmt inner
where inner.nestedIn(outer) and
      getAnIterationVariable(outer) = getAnIterationVariable(inner)
select inner.getTest(), "This for statement uses the same loop variable as an enclosing $@.",
                        outer, "for statement"
