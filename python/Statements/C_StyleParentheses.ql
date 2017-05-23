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
 * @name C-style condition
 * @description Putting parentheses around a condition in an 'if' or 'while' statement is
 *              unnecessary and harder to read.
 * @kind problem
 * @tags maintainability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 */

import python

from Expr e, Location l, string kind, string what
where e.isParenthesised() and
not e instanceof Tuple and
(
    exists(If i | i.getTest() = e) and kind = "if" and what = "condition"
    or
    exists(While w | w.getTest() = e) and kind = "while" and what = "condition"
    or
    exists(Return r | r.getValue() = e) and kind = "return" and what = "value"
    or
    exists(Assert a | a.getTest() = e and not exists(a.getMsg())) and kind = "assert" and what = "test"
)
and
l = e.getLocation() and l.getStartLine() = l.getEndLine()
select e, "Parenthesised " + what + " in '" + kind + "' statement."
