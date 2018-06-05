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
 * @name Nested loops with same variable reused after inner loop body
 * @description Redefining a variable in an inner loop and then using
 *              the variable in an outer loop causes unexpected behavior.
 * @kind problem
 * @tags maintainability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/nested-loops-with-same-variable-reused
 */

import python

predicate loop_variable_ssa(For f, Variable v, SsaVariable s) {
    f.getTarget().getAFlowNode() = s.getDefinition() and v = s.getVariable()
}

predicate variableUsedInNestedLoops(For inner, For outer, Variable v, Name n) {
    /* Ignore cases where there is no use of the variable or the only use is in the inner loop. */
    outer.contains(n)
    and not inner.contains(n)
    /* Only treat loops in body as inner loops. Loops in the else clause are ignored. */
    and outer.getBody().contains(inner)
    and exists(SsaVariable s |
        loop_variable_ssa(inner, v, s.getAnUltimateDefinition())
        and loop_variable_ssa(outer, v, _)
        and s.getAUse().getNode() = n
    )
}

from For inner, For outer, Variable v, Name n
where variableUsedInNestedLoops(inner, outer, v, n)
select inner, "Nested for statement $@ loop variable '" + v.getId() + "' of enclosing $@.", n, "uses",
       outer, "for statement"