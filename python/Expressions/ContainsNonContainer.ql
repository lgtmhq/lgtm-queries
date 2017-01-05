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
 * @name Membership test with a non-container
 * @description A membership test, such as 'item in sequence', with a non-container on the right hand side will raise a 'TypeError'.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 */

import python

predicate rhs_in_expr(ControlFlowNode rhs, Compare cmp) {
    exists(Cmpop op, int i | cmp.getOp(i) = op and cmp.getComparator(i) = rhs.getNode() |
           op instanceof In or op instanceof NotIn
    )
}

from ControlFlowNode non_seq, Compare cmp, ClassObject cls, ControlFlowNode origin
where rhs_in_expr(non_seq, cmp) and
non_seq.refersTo(_, cls, origin) and
not cls.failedInference() and
not cls.hasAttribute("__contains__") and
not cls.hasAttribute("__iter__") and
not cls.hasAttribute("__getitem__") and
not cls = theNoneType()

select cmp, "This test may raise an Exception as the $@ may be of non-container class $@.", origin, "target", cls, cls.getName()