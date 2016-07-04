// Copyright 2016 Semmle Ltd.
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
 * @name Inconsistent equals and hashCode
 * @description If a class overrides only one of 'equals' and 'hashCode', it may mean that 
 *              'equals' and 'hashCode' are inconsistent.
 * @kind problem
 * @problem.severity error
 * @cwe 581
 */
import default
import Equality

from Class c, string message, Method existingMethod
where c.fromSource() and 
  (
    not exists(EqualsMethod e | e.getDeclaringType() = c) 
    and exists(HashCodeMethod h | h.getDeclaringType() = c and h = existingMethod) 
    and message = "Class " + c.getName() + " overrides $@ but not equals."
    or 
    not exists(HashCodeMethod h | h.getDeclaringType() = c) 
    // If the inherited `equals` is a refining `equals` then the superclass hash code is still valid.
    and exists(EqualsMethod e | e.getDeclaringType() = c and e = existingMethod and not e instanceof RefiningEquals) 
    and message = "Class " + c.getName() + " overrides $@ but not hashCode."
  ) 
select c, message, existingMethod, existingMethod.getName()
