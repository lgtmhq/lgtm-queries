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
 * @name Useless class
 * @description Class only defines one public method (apart from __init__ or __new__) and should be replaced by a function
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       useless-code
 */

import python

predicate fewer_than_two_public_methods(Class cls, int methods) {
    (methods = 0 or methods = 1) and
    methods = count(Function f | f = cls.getAMethod() and not f = cls.getInitMethod())
}

predicate does_not_define_special_method(Class cls) {
    not exists(Function f | f = cls.getAMethod() and f.isSpecialMethod())
}


predicate no_inheritance(Class c) {
    not exists(ClassObject cls, ClassObject other |
        cls.getPyClass() = c and 
        other != theObjectType() |
        other.getABaseType() = cls or
        cls.getABaseType() = other
    )
    and
    not exists(Expr base | base = c.getABase() |
        not base instanceof Name or ((Name)base).getId() != "object"
    )
}

predicate is_decorated(Class c) {
    exists(c.getADecorator())
}

predicate is_stateful(Class c) {
    exists(Function method, ExprContext ctx | 
        method.getScope() = c and (ctx instanceof Store or ctx instanceof AugStore) |
        exists(Subscript s | s.getScope() = method and s.getCtx() = ctx)
        or
        exists(Attribute a | a.getScope() = method and a.getCtx() = ctx)
    )
    or
    exists(Function method, Call call, Attribute a, string name | 
        method.getScope() = c and call.getScope() = method and 
        call.getFunc() = a and a.getName() = name |
        name = "pop" or name = "remove" or name = "discard" or
        name = "extend" or name = "append"
    )
 
}

predicate useless_class(Class c, int methods) {
    c.isTopLevel()
    and
    c.isPublic()
    and
    no_inheritance(c)
    and
    fewer_than_two_public_methods(c, methods)
    and
    does_not_define_special_method(c)
    and
    not c.isProbableMixin()
    and
    not is_decorated(c)
    and
    not is_stateful(c)
}

from Class c, int methods, string msg
where useless_class(c, methods) and
(methods = 1 and msg = "Class " + c.getName() + " defines only one public method, which should be replaced by a function."
 or
 methods = 0 and msg = "Class " + c.getName() + " defines no public methods and could be replaced with a namedtuple or dictionary."
)
select c, msg
