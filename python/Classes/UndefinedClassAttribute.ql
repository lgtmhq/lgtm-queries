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
 * @name Undefined class attribute
 * @description Accessing an attribute of 'self' that is not initialized anywhere in the class in the __init__ method may cause a AttributeError at runtime
 * @kind problem
 * @problem.severity error
 */

import python
import semmle.python.SelfAttribute

predicate undefined_class_attribute(SelfAttributeRead a, CheckClass c, int line) {
    not c.sometimesDefines(a.getName()) and
    c.interestingUndefined(a) and
    line = a.getLocation().getStartLine()
}

predicate report_undefined_class_attribute(Attribute a, ClassObject c) {
    exists(int line |
        undefined_class_attribute(a, c, line) and
        line = min(int x | undefined_class_attribute(_, c, x))
    )
}

from Attribute a, ClassObject c
where report_undefined_class_attribute(a, c)
select a, "Attribute '" +  a.getName() + "' is not defined in either the class body or in any method"

