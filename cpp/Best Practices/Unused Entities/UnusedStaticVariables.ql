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
 * @name Unused static variable
 * @description A static variable that is never accessed may be an indication
 *              that the code is incomplete or has a typo.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @tags efficiency
 *       useless-code
 *       external/cwe/cwe-563
 */
import default

predicate declarationHasSideEffects(Variable v) {
  exists (Class c | c = v.getType().getUnderlyingType().getUnspecifiedType() |
    c.hasConstructor() or c.hasDestructor()
  )
}

from Variable v
where v.isStatic()
  and v.hasDefinition()
  and not exists(VariableAccess a | a.getTarget() = v)
  and not v instanceof MemberVariable
  and not declarationHasSideEffects(v)
  and not v.getAnAttribute().hasName("used")
select v, "Static variable " + v.getName() + " is never read"
