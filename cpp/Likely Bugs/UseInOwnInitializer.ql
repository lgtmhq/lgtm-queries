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
 * @name Variable used in its own initializer
 * @id cpp/use-in-own-initializer
 * @description Loading from a variable in its own initializer may lead to undefined behavior.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags maintainability
 *       correctness
 */

import cpp

from Initializer init, Variable v, VariableAccess va
where init.getDeclaration() = v
  and va.getTarget() = v
  and va.getParent*() = init
  and (
    va.hasLValueToRValueConversion() or
    exists (Assignment assn | assn.getLValue() = va) or
    exists (CrementOperation crement | crement.getAnOperand() = va)
  )
  and not va.isUnevaluated()
select va, v.getName() + " is used in its own initializer."
