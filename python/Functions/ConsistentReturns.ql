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
 * @name Explicit returns mixed with implicit (fall through) returns
 * @description Mixing implicit and explicit returns indicates a likely error as implicit returns always return 'None'.
 * @kind problem
 * @tags reliability
 *       maintainability
 * @problem.severity recommendation
 * @sub-severity high
 * @precision high
 * @id py/mixed-returns
 */

import python

predicate explicitly_returns_non_none(Function func) {
    exists(Return return | return.getScope() = func and
           exists(Expr val |
                  val= return.getValue() |
                  not val instanceof None
           )
    )
}

predicate has_implicit_return(Function func) {
    exists(ControlFlowNode fallthru | fallthru = func.getFallthroughNode() and not fallthru.unlikelyReachable()) or
    exists(Return return | return.getScope() = func and not exists(return.getValue()))
}


from Function func
where explicitly_returns_non_none(func) and has_implicit_return(func)
select func, "Mixing implicit and explicit returns may indicate an error as implicit returns always return None."
