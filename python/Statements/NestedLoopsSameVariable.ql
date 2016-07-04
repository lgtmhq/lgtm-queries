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
 * @name Nested loops with same variable
 * @description Nested loops in which the target variable is the same for each loop make
 *              the behavior of the loops difficult to understand.
 * @kind problem
 * @problem.severity warning
 */
import python

predicate loop_variable(For f, Variable v) {
    f.getTarget().defines(v)
}

predicate nestedForViolation(For inner, For outer, Variable v) {
    /* Only treat loops in body as inner loops. Loops in the else clause are ignored. */
    outer.getBody().contains(inner) and loop_variable(inner, v) and loop_variable(outer, v)
    /* Ignore cases where there is no use of the variable or the only use is in the inner loop */
    and exists(Name n | n.uses(v) and outer.contains(n) and not inner.contains(n))
}

from For inner, For outer, Variable v
where nestedForViolation(inner, outer, v)
select inner, "Nested for statement uses loop variable '" + v.getId() + "' of enclosing $@.",
       outer, "for statement"
