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

import default

/* Whether 'func' includes super().xxx where 'xxx' is the name of 'func' */
private predicate uses_super(FunctionObject func) {
    exists(Attribute a, Call c, GlobalVariable sup |
        a.getObject() = c and
        c.getFunc() = sup.getAnAccess() and
        sup.getId() = "super" and
        c.getScope() = func.getFunction() and
        a.getName() = func.getName()
    )
}

/**
 * Whether function `func` calls `super_type.called`
 * In the following code:
 * 
 *   def func(self):
 *     T.func(self)
 *
 * called is `T.func` and super_type is `T`
 */
private predicate direct_call(FunctionObject func, ClassObject super_type, FunctionObject called) {
    exists(Call c, string name |
        func.getName() = name and
        c.getScope() = func.getFunction() and
        c.getAFlowNode().getFunction().(AttrNode).getObject(name).refersTo(super_type) and
        ((Name)c.getArg(0)).getId() = "self" and
        called = super_type.lookupAttribute(name)
    )
}

/** Returns the function of the same name whose enclosing class is a superclass of the class enclosing 'func'
    and which is called by 'func', either directly: SuperType.meth() or indirectly: super(Type, self).meth(),
    when the initial call, from which this chain derives, has 'self' which an instance of 'self_type' */
FunctionObject next_function_in_chain(ClassObject self_type, FunctionObject func) {
    exists(ClassObject current, string name | current.declaredAttribute(name) = func |
        uses_super(func) and
        exists(ClassObject sup | sup = self_type.nextInMro(current) |
            result = sup.lookupAttribute(name)
        )
    )
    or
    exists(ClassObject base |
        direct_call(func, base, result) and 
        base = self_type.getASuperType() and
        (self_type.lookupAttribute(_) = func or func = next_function_in_chain(self_type, _))
    )
}
