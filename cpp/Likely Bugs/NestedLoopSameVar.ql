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
 * @description When a nested loop uses the same iteration variable as its outer loop, the
 *   behavior of the outer loop easily becomes difficult to understand as the
 *   inner loop will affect its control flow. It is likely to be a typo.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags maintainability
 *       correctness
 */
import NestedLoopSameVar

from ForStmt inner, Variable iteration, ForStmt outer
where nestedForViolation(inner, iteration, outer)
select inner.getCondition(), "Nested for statement uses loop variable $@ of enclosing $@.", iteration, iteration.getName(), outer, "for statement"
