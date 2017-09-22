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
 * @name Complex condition
 * @description Boolean expressions that are too deeply nested are hard to read and understand. Consider naming intermediate results as local variables.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @tags testability
 *       readability
 *       maintainability
 */
import default

predicate logicalOp(string op) {
  op = "&&" or op = "||"
}

predicate nontrivialLogicalOperator(Operation e) {
  exists(string op |
    op = e.getOperator() and
    logicalOp(op) and
    not (op = e.getParent().(Operation).getOperator())
  )
  and not e.isInMacroExpansion()
}

from Expr e, int operators
where not (e.getParent() instanceof Expr)
      and operators = count(Operation op | op.getParent*() = e and nontrivialLogicalOperator(op))
      and operators > 5
select e, "Complex condition: too many logical operations in this expression."
