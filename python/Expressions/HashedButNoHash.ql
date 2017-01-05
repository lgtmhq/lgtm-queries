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
 * @name Unhashable object hashed
 * @description Hashing an object which is not hashable will result in a TypeError at runtime.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 */

import python

/* This assumes that any indexing operation where the value is not a sequence or numpy array involves hashing.
 * For sequences, the index must be an int ,which are hashable, so we don't need to treat them specially.
 * For numpy arrays, the index may be a list, which are not hashable and needs to be treated specially.
 */
 
predicate numpy_array_type(ClassObject na) {
    exists(ModuleObject np | np.getName() = "numpy" or np.getName() = "numpy.core" |
        na.getAnImproperSuperType() = np.getAttribute("ndarray")
    )
}

predicate has_custom_getitem(ClassObject cls) {
    cls.lookupAttribute("__getitem__") instanceof PyFunctionObject
    or
    numpy_array_type(cls)
}

predicate explicitly_hashed(ControlFlowNode f) {
     exists(CallNode c, GlobalVariable hash | c.getArg(0) = f and c.getFunction().(NameNode).uses(hash) and hash.getId() = "hash")
}

predicate unhashable_subscript(ControlFlowNode f, ClassObject c) {
    is_unhashable(f, c) and
    exists(SubscriptNode sub | sub.getIndex() = f |
        exists(ClassObject custom_getitem |
            sub.getValue().refersTo(_, custom_getitem, _) and
            not has_custom_getitem(custom_getitem)
        )
    )
}

predicate is_unhashable(ControlFlowNode f, ClassObject cls) {
    f.refersTo(_, cls, _) and
    (not cls.hasAttribute("__hash__") and not cls.unknowableAttributes() and cls.isNewStyle()
     or
     cls.lookupAttribute("__hash__") = theNoneObject()
    )
}

from ControlFlowNode f, ClassObject c
where 
explicitly_hashed(f) and is_unhashable(f, c)
or
unhashable_subscript(f, c)
select f.getNode(), "This instance of $@ is unhashable.", c, c.getQualifiedName()
