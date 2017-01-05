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
 * @name Redundant assignment
 * @description Assigning a variable to itself is useless and very likely indicates an error in the code.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       useless-code
 */

import python
predicate assignment(AssignStmt a, Expr left, Expr right)
{
    a.getATarget() = left and a.getValue() = right
}

predicate corresponding(Expr left, Expr right) {
    assignment(_, left, right)
    or
    exists(Attribute la, Attribute ra |
        corresponding(la, ra) and
        left = la.getObject() and
        right = ra.getObject())
}

predicate same_value(Expr left, Expr right) {
    same_name(left, right)
    or
    same_attribute(left, right)
}

predicate maybe_defined_in_outer_scope(Name n) {
    exists(SsaVariable v | v.getAUse().getNode() = n |
        v.maybeUndefined()
    )
}

Variable relevant_var(Name n) {
	n.getVariable() = result and
	(corresponding(n, _) or corresponding(_, n))
}

predicate same_name(Name n1, Name n2) {
    corresponding(n1, n2) and
    relevant_var(n1) = relevant_var(n2) and
    not exists(builtin_object(n1.getId())) and
    not maybe_defined_in_outer_scope(n2)
}

ClassObject value_type(Attribute a) {
    a.getObject().refersTo(_, result, _)
}

predicate is_property_access(Attribute a) {
    value_type(a).lookupAttribute(a.getName()) instanceof PropertyObject
}

predicate same_attribute(Attribute a1, Attribute a2) {
    corresponding(a1, a2) and a1.getName() = a2.getName() and same_value(a1.getObject(), a2.getObject()) and
    exists(value_type(a1)) and not is_property_access(a1)
}

int pyflakes_commented_line(File file) {
    exists(Comment c | c.getText().toLowerCase().matches("%pyflakes%") |
        c.getLocation().hasLocationInfo(file.getName(), result, _, _, _)
    )
}

predicate pyflakes_commented(AssignStmt assignment) {
    exists(Location loc |
        assignment.getLocation() = loc and
        loc.getStartLine() = pyflakes_commented_line(loc.getFile()))
}

from AssignStmt a, Expr left, Expr right
where assignment(a, left, right)
  and same_value(left, right)
  and not pyflakes_commented(a)
select a, "This assignment assigns a variable to itself."
