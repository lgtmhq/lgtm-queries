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
 * @name Builtin shadowed by local variable
 * @description Defining a local variable with the same name as a built-in object
 *              makes the built-in object unusable within the current scope and makes the code
 *              more difficult to read.
 * @kind problem
 * @tags maintainability
 *       readability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 * @id py/local-shadows-builtin
 */
 
import python
import Shadowing
 
predicate white_list(string name) {
    /* These are rarely used and thus unlikely to be confusing */
    name = "iter" or
    name = "next" or
    name = "input" or
    name = "file" or
    name = "apply" or
    name = "slice" or
    name = "buffer" or
    name = "coerce" or
    name = "intern" or
    name = "exit" or
    name = "quit" or
    name = "license" or
    /* These are short and/or hard to avoid */
    name = "dir" or
    name = "id" or
    name = "max" or
    name = "min" or
    name = "sum" or
    name = "cmp" or
    name = "chr" or
    name = "ord" or
    name = "bytes" or
    name = "_"
}

predicate shadows(Name d, string name, Scope scope, int line) {
    exists(LocalVariable l | d.defines(l) and scope instanceof Function and
           l.getId() = name and
           exists(builtin_object(l.getId()))
    ) and
    d.getScope() = scope and
    d.getLocation().getStartLine() = line and
    not white_list(name) and
    not optimising_parameter(d)
}

predicate first_shadowing_definition(Name d, string name) {
    exists(int first, Scope scope |
        shadows(d, name, scope, first) and
        first = min(int line | shadows(_, name, scope, line)))
}

from Name d, string name
where first_shadowing_definition(d, name)
select d, "Local variable " + name + " shadows a builtin variable."
