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
 * @name Unreachable 'except' block
 * @description Handling general exceptions before specific exceptions means that the specific
 *              handlers are never executed.
 * @kind problem
 * @tags reliability
 *       maintainability
 *       external/cwe/cwe-561
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/unreachable-except
 */

import python

predicate incorrect_except_order(ExceptStmt ex1, ClassObject cls1, ExceptStmt ex2, ClassObject cls2) {
   exists(int i, int j, Try t | 
       ex1 = t.getHandler(i) and
       ex2 = t.getHandler(j) and i < j and
       cls1 = except_class(ex1) and
       cls2 = except_class(ex2) and
       cls1 = cls2.getASuperType()
   )
}

ClassObject except_class(ExceptStmt ex) {
    ex.getType().refersTo(result)
}

from ExceptStmt ex1, ClassObject cls1, ExceptStmt ex2, ClassObject cls2
where incorrect_except_order(ex1, cls1, ex2, cls2)
select ex2, "Except block for $@ is unreachable; the more general $@ for $@ will always be executed in preference.",
       cls2, cls2.getName(), ex1, "except block", cls1, cls1.getName()
