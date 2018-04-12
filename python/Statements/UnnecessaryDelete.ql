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
 * @name Unnecessary delete statement in function
 * @description Using a 'delete' statement to delete a local variable is
 *              unnecessary, because the variable is deleted automatically when
 *              the function exits.
 * @kind problem
 * @tags maintainability
 *       useless-code
 * @problem.severity warning
 * @sub-severity low
 * @precision high
 * @id py/unnecessary-delete
 */


import python

from Delete del, Expr e, Function f
where
    f.getLastStatement() = del and
    e = del.getATarget() and
    f.containsInScope(e) and
    not e instanceof Subscript and
    not e instanceof Attribute and
    not exists(Stmt s | s.(While).contains(del) or s.(For).contains(del)) and
    /* False positive: calling `sys.exc_info` within a function results in a
       reference cycle,and an explicit call to `del` helps break this cycle. */
    not exists(FunctionObject ex |
        ex.hasLongName("sys.exc_info") and
        ex.getACall().getScope() = f
    )
select del, "Unnecessary deletion of local variable $@ in function $@.",
    e.getLocation(), e.toString(), f.getLocation(), f.getName()