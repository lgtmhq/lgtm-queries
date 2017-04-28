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
 *       external/cwe/cwe-480
 *       external/cwe/cwe-561
 * @precision high
 */

import Clones
import DOMProperties

/**
 * Gets a description of expression `e`, which is assumed to be the left-hand
 * side of an assignment.
 *
 * For variable accesses, the description is the variable name. For property
 * accesses, the description is of the form `"property <name>"`, where
 * `<name>` is the name of the property, except if `<name>` is a numeric index,
 * in which case `element <name>` is used instead.
 */
string describe(Expr e) {
  exists (VarAccess va | va = e | result = "variable " + va.getName())
  or
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