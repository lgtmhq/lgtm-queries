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
 * @name Redundant comparison
 * @description The result of a comparison is implied by a previous comparison. 
 * @kind problem
 * @problem.severity warning
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

from Expr test, Expr other, boolean isTrue, string message
where 
forex(Comparison comp | 
    comp.getNode() = test | 
    exists(ConditionBlock other_comp | useless_test(comp, other_comp, isTrue) and other_comp.getLastNode().getNode() = other)
)
and (
    if exists(test.(Compare).getOp(1)) then
        message = "Part of test is always " + isTrue + ", because of $@"
    else
        message = "Test is always " + isTrue + ", because of $@"
    )
select test, message, other, "this condition"
