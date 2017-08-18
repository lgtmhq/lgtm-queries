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
 * @name Implicit string concatenation in a list
 * @description Omitting a comma between strings causes implicit concatenation which is confusing in a list.
 * @kind problem
 * @tags reliability
 *       maintainability
 *       convention
 * @problem.severity warning
 * @sub-severity high
 * @precision high
 * @id py/implicit-string-concatenation-in-list
 */

import python

predicate string_const(Expr s) {
    s instanceof StrConst
    or
    string_const(s.(BinaryExpr).getLeft()) and string_const(s.(BinaryExpr).getRight())
}

from StrConst s
where
// Implicitly concatenated string is in a list and that list contains at least one other string.
exists(List l, Expr other |
    not s = other and
    l.getAnElt() = s and
    l.getAnElt() = other and
    string_const(other)
) and
exists(s.getAnImplicitlyConcatenatedPart()) and
not s.isParenthesised()

select s, "Implicit string concatenation. Maybe missing a comma?"
