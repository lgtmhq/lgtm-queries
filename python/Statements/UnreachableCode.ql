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
 * @name Unreachable code
 * @description Code is unreachable
 * @kind problem
 * @problem.severity warning
 */

import python

predicate is_unreachable(Stmt s) {
    not exists(ControlFlowNode flow | flow.getNode() = s)
    or
    exists(If i | unreachable_in_if(i, s))
    or
    exists(While w | unreachable_in_while(w, s))
}

predicate unreachable_in_if(If ifstmt, Stmt s) {
    ifstmt.getTest().(ImmutableLiteral).booleanValue() = false and ifstmt.getBody().contains(s)
    or
    ifstmt.getTest().(ImmutableLiteral).booleanValue() = true and ifstmt.getOrelse().contains(s)
}

predicate unreachable_in_while(While whilestmt, Stmt s) {
    whilestmt.getTest().(ImmutableLiteral).booleanValue() = false and whilestmt.getBody().contains(s)
}

predicate reportable_unreachable(Stmt s) {
    is_unreachable(s) and  
    not exists(Stmt other | is_unreachable(other) |
        other.contains(s)
        or
        exists(StmtList l, int i, int j | 
            l.getItem(i) = other and l.getItem(j) = s and i < j
        )
    )
}

from Stmt s
where reportable_unreachable(s)
select s, "Unreachable statement."
