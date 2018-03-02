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
 * @name Unclear comparison precedence
 * @description Using comparisons as operands of other comparisons is unusual
 *              in itself, and most readers will require parentheses to be sure
 *              of the precedence.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/comparison-precedence
 * @tags maintainability
 *       readability
 */
import cpp


from ComparisonOperation co, ComparisonOperation chco
where co.getAChild() = chco and not chco.isParenthesised()
select co, "Check the comparison operator precedence."
