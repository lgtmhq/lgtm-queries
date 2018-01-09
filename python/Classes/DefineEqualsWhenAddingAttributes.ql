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
 * @name __eq__ not overridden when adding attributes
 * @description When adding new attributes to instances of a class, equality for that class needs to be defined.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity warning
 * @sub-severity high
 * @precision high
 * @id py/missing-equals
 */

import python
import semmle.python.SelfAttribute
import Equality

predicate class_stores_to_attribute(ClassObject cls, SelfAttributeStore store, string name) {
    exists(FunctionObject f | f = cls.declaredAttribute(_) and store.getScope() = f.getFunction() and store.getName() = name) and
    /* Exclude classes used as metaclasses */
    not cls.getASuperType() = theTypeType()
}

predicate should_override_eq(ClassObject cls, Object base_eq) {
    not cls.declaresAttribute("__eq__") and
    exists(ClassObject sup | sup = cls.getABaseType() and sup.declaredAttribute("__eq__") = base_eq |
        not exists(GenericEqMethod eq | eq.getScope() = sup.getPyClass()) and
        not exists(IdentityEqMethod eq | eq.getScope() = sup.getPyClass()) and
        not base_eq.(FunctionObject).getFunction() instanceof IdentityEqMethod and
        not base_eq = theObjectType().declaredAttribute("__eq__")
    )
}

/** Does the non-overridden __eq__ method access the attribute,
 * which implies that the  __eq__ method does not need to be overridden.
 */
predicate superclassEqExpectsAttribute(ClassObject cls, PyFunctionObject base_eq, string attrname) {
    not cls.declaresAttribute("__eq__") and
    exists(ClassObject sup | sup = cls.getABaseType() and sup.declaredAttribute("__eq__") = base_eq |
        exists(SelfAttributeRead store |
            store.getName() = attrname |
            store.getScope() = base_eq.getFunction()
        )
    )
}

from ClassObject cls, SelfAttributeStore store, Object base_eq
where class_stores_to_attribute(cls, store, _) and should_override_eq(cls, base_eq) and
/* Don't report overridden unittest.TestCase. -- TestCase overrides __eq__, but subclasses do not really need to. */
not cls.getASuperType().getName() = "TestCase" and
not superclassEqExpectsAttribute(cls, base_eq, store.getName())

select cls, "The class '" + cls.getName() + "' does not override $@, but adds the new attribute $@.", base_eq,  "'__eq__'", store, store.getName()
