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
 * @name Self assignment
 * @description Assigning a variable to itself has no effect.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 */

import Clones
import DOMProperties

string describe(Expr e) {
  exists (VarAccess va | va = e | result = "variable " + va.getName()) or
  exists (string name | name = e.(PropAccess).getPropertyName() |
    if exists(name.toInt()) then
      result = "element " + name
    else
      result = "property " + name
  )
}

from SelfAssignment e, string dsc
where e.same(_) and
      dsc = describe(e) and
      // exclude properties for which there is an accessor somewhere
      not exists(PropertyAccessor acc | acc.getName() = e.(PropAccess).getPropertyName()) and
      // exclude DOM properties
      not isDOMProperty(e.(PropAccess).getPropertyName())
select e.getParent(), "This expression assigns " + dsc + " to itself."