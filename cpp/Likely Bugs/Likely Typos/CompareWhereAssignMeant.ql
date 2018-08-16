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
 * @name Comparison where assignment was intended
 * @description The '==' operator may have been used accidentally, where '='
 *              was intended, resulting in a useless test.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/compare-where-assign-meant
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-482
 */
import cpp

from ExprInVoidContext op
where op instanceof EQExpr
      or
      op.(FunctionCall).getTarget().hasName("operator==")
select op, "This '==' operator has no effect. The assignment ('=') operator was probably intended."
