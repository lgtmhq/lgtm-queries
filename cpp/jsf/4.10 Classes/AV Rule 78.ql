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
 * @name No virtual destructor
 * @description All base classes with a virtual function must define a virtual destructor. If an application attempts to delete a derived class object through a base class pointer, the result is undefined if the base class destructor is non-virtual.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @tags reliability
 *       readability
 *       language-features
 */
import default

// find classes with virtual functions that have a destructor that is not virtual and for which there exists a derived class
// when calling the destructor of a derived class the destructor in the base class may not be called

from Class c
where exists(VirtualFunction f | f.getDeclaringType() = c)
  and exists(Destructor d | d.getDeclaringType() = c and not d.isVirtual())
  and exists(ClassDerivation d | d.getBaseClass() = c)
select c, "Base classes with a virtual function must define a virtual destructor."
