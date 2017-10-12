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
 * @name Redefined default parameter
 * @description An inherited default parameter shall never be redefined. Default values are bound statically which is confusing when combined with dynamically bound function calls.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/redefined-default-parameter
 * @tags maintainability
 *       readability
 */
import default

from Parameter p, Parameter superP, MemberFunction subF, MemberFunction superF, int i, string subValue, string superValue
where p.hasInitializer()
  and subF.getParameter(i) = p
   and superP.hasInitializer()
   and subF.overrides(superF)
   and superF.getParameter(i) = superP
   and subValue = p.getInitializer().getExpr().getValue()
   and superValue = superP.getInitializer().getExpr().getValue()
   and subValue != superValue
select p.getInitializer().getExpr(),
   "Parameter " + p.getName() +
   " redefines its default value to " + subValue +
   " from the inherited default value " + superValue +
   " (in " + superF.getDeclaringType().getName() +
   ").\nThe default value will be resolved statically, not by dispatch, so this can cause confusion."
