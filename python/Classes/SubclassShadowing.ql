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
 * @name Superclass attribute shadows subclass method
 * @description Defining an attribute in a superclass method with a name that matches a subclass
 *              method, hides the method in the subclass.
 * @kind problem
 * @problem.severity error
 */

/* Determine if a class defines a method that is shadowed by an attribute
   defined in a super-class
*/

/* Need to find attributes defined in superclass (only in __init__?) */

import python

predicate shadowed_by_super_class(ClassObject c, ClassObject supercls, Assign assign, FunctionObject f)
{
    c.getASuperType() = supercls and c.declaredAttribute(_) = f and
    exists(FunctionObject init, Attribute attr |
        supercls.declaredAttribute("__init__") = init and
        attr = assign.getATarget() and
        ((Name)attr.getObject()).getId() = "self" and
        attr.getName() = f.getName() and
        assign.getScope() = ((FunctionExpr)init.getOrigin()).getInnerScope()
    ) and
    /* It's OK if the super class defines the method as well. 
     * We assume that the original method must have been defined for a reason. */
    not supercls.hasAttribute(f.getName())
}

from ClassObject c, ClassObject supercls, Assign assign, FunctionObject shadowed
where shadowed_by_super_class(c, supercls, assign, shadowed)
select shadowed.getOrigin(), "Method " + shadowed.getName() + " is shadowed by $@ in super class '"+ supercls.getName() + "'.", assign, "an attribute"

