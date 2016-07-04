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
 * @name Constant in conditional expression or statement
 * @description The conditional is always true or always false
 * @kind problem
 * @problem.severity warning
 */

import python


predicate is_condition(Expr cond) {
	exists(If i | i.getTest() = cond) or
	exists(IfExp ie | ie.getTest() = cond)
}

/* Treat certain unmodified builtins as constants as well */
predicate effective_constant(Name cond) {
    exists(GlobalVariable var | var = cond.getVariable() and not exists(NameNode f | f.defines(var)) |
                                var.getId() = "True" or var.getId() = "False" or var.getId() = "NotImplemented"
    )
}

from Expr cond
where is_condition(cond) and (cond.isConstant() or effective_constant(cond))
select cond, "Testing a constant will always give the same result."
