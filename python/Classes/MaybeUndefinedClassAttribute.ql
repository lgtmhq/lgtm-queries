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
 * @name Maybe undefined class attribute
 * @description Accessing an attribute of 'self' that is not initialized in the __init__ method may cause a AttributeError at runtime
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 */

import python
import semmle.python.SelfAttribute

predicate guarded_by_other_attribute(SelfAttributeRead a, CheckClass c) {
    c.sometimesDefines(a.getName()) and
    exists(SelfAttributeRead guard, If i | 
        i.contains(a) and
        c.assignedInInit(guard.getName()) |
        i.getTest() = guard
        or
        i.getTest().contains(guard)
    )
}


predicate maybe_undefined_class_attribute(SelfAttributeRead a, CheckClass c) {
    c.sometimesDefines(a.getName()) and
    not c.alwaysDefines(a.getName()) and
    c.interestingUndefined(a) and 
    not guarded_by_other_attribute(a, c)
}

from Attribute a, ClassObject c, SelfAttributeStore sa
where maybe_undefined_class_attribute(a, c) and 
sa.getClass() = c.getPyClass() and sa.getName() = a.getName()
select a, "Attribute '" +  a.getName() + 
"' is not defined in the class body nor in the __init__() method, but it is defined $@", sa, "here"

