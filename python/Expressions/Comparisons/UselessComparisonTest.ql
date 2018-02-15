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
 * @name Redundant comparison
 * @description The result of a comparison is implied by a previous comparison.
 * @kind problem
 * @tags useless-code
 *       external/cwe/cwe-561
 *       external/cwe/cwe-570
 *       external/cwe/cwe-571
 * @problem.severity warning
 * @sub-severity high
 * @precision high
 * @id py/redundant-comparison
 */

import python
import semmle.python.Comparisons


/** A test is useless if for every block that it controls there is another test that is at least as
 * strict and also controls that block.
 */
private predicate useless_test(Comparison comp, ComparisonControlBlock controls, boolean isTrue) {
    controls.impliesThat(comp.getBasicBlock(), comp, isTrue) and
    /* Exclude complex comparisons of form `a < x < y`, as we do not (yet) have perfect flow control for those */
    not exists(controls.getTest().getNode().(Compare).getOp(1))
}

private predicate useless_test_ast(AstNode comp, AstNode previous, boolean isTrue) {
    forex(Comparison compnode, ConditionBlock block| 
        compnode.getNode() = comp and
        block.getLastNode().getNode() = previous
        |
        useless_test(compnode, block, isTrue)
    )
}

from Expr test, Expr other, boolean isTrue
where 
useless_test_ast(test, other, isTrue) and not useless_test_ast(test.getAChildNode+(), other, _)


select test, "Test is always " + isTrue + ", because of $@", other, "this condition"
