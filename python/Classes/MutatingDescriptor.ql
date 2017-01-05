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
 * @name Mutation of descriptor in __get__ or __set__ method.
 * @description Descriptor objects can be shared across many instances. Mutating them can cause strange side effects or race conditions.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 */

import python

predicate mutates_descriptor(ClassObject cls, SelfAttributeStore s) {
    cls.isDescriptorType() and
    exists(PyFunctionObject f |
        cls.lookupAttribute(_) = f and 
        not f.getName() = "__init__" and
        s.getScope() = f.getFunction()
    )
}

from ClassObject cls, SelfAttributeStore s
where
mutates_descriptor(cls, s)

select s, "Mutation of descriptor $@ object may lead to action-at-a-distance effects or race conditions for properties.", cls, cls.getName()