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
 * @name Statement has no effect
 * @description A statement has no effect
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       useless-code
 */

import python

/* Conservative estimate of whether attribute lookup has a side effect */
predicate maybe_side_effecting_attribute(Attribute attr) {
    exists(string name, ClassObject cls |
        attr.getObject().refersTo(_, cls, _) and
        attr.getName() = name |
        exists(Object val |
            val = cls.lookupAttribute(name) |
            side_effecting_dcesrciptor_type(val.getAnInferredType())
            or
            /* If we don't know the type, we have to assume it may cause a side effect */
            not exists(val.getAnInferredType())
        )
    )
}

predicate side_effecting_dcesrciptor_type(ClassObject descriptor) {
    descriptor.isDescriptorType() and
    /* Technically all descriptor gets have side effects, 
     * but some are indicative of a missing call and 
     * we want to treat them as having no effect. */
   not descriptor = thePyFunctionType() and
   not descriptor = theStaticMethodType() and
   not descriptor = theClassMethodType()
}

predicate no_effect(Expr e) {
    not e instanceof StrConst and
    not ((StrConst)e).isDocString() and
    not e.hasSideEffects() and
    not maybe_side_effecting_attribute(e.getASubExpression*())
}

from ExprStmt stmt
where no_effect(stmt.getValue())
select stmt, "This statement has no effect."