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
 * @name Inconsistent virtual inheritance
 * @description A base class shall not be both virtual and non-virtual in the same hierarchy.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/inconsistent-virtual-inheritance
 * @tags maintainability
 *       readability
 */
import default

predicate derivesVirtual(Class c, Class base) {
  exists(ClassDerivation d | d.getDerivedClass() = c and d.getBaseClass() = base
    and d.hasSpecifier("virtual"))
  or derivesVirtual(c.getABaseClass(), base)
}

predicate derivesNonVirtual(Class c, Class base) {
  exists(ClassDerivation d | d.getDerivedClass() = c and d.getBaseClass() = base
    and not d.hasSpecifier("virtual"))
  or derivesNonVirtual(c.getABaseClass(), base)
}

from Class c, Class base
where c.getABaseClass+() = base
  and derivesVirtual(c, base)
  and derivesNonVirtual(c, base)
select c, "AV Rule 89: The base class " + base.getName() + " is derived both virtual and non-virtual."
