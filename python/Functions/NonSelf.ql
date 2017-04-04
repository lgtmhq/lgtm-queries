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
 * @name First argument of a method is not named 'self'
 * @description Using an alternative name for the first argument of an instance method makes
 *              code more difficult to read; PEP8 states that the first argument to instance
 *              methods should be 'self'.
 * @kind problem
 * @tags maintainability
 *       readability
 *       convention
 * @problem.severity recommendation
 * @sub-severity high
 * @precision very-high
 */

import python
import semmle.python.libraries.Zope

predicate first_arg_self(Function f) {
    f.getArgName(0) = "self"
}

predicate is_type_method(FunctionObject f) {
    exists(ClassObject c | c.lookupAttribute(_) = f and c.getASuperType() = theTypeType())
}

predicate used_in_defining_scope(FunctionObject f) {
    exists(Call c | 
        c.getScope() = f.getFunction().getScope() and
        c.getFunc().refersTo(f)
    )
}

from Function f, PyFunctionObject func, string message
where
exists(ClassObject cls, string name | 
    cls.declaredAttribute(name) = func and cls.isNewStyle() and
    not name = "__new__" and
    /* declared in scope */
    f.getScope() = cls.getPyClass()
) and
not first_arg_self(f) and not is_type_method(func) and
func.getFunction() = f and not f.getName() = "lambda" and
not used_in_defining_scope(func) and
(
  if exists(f.getArgName(0)) then
      message = "Normal methods should have 'self', rather than '" + f.getArgName(0) + "', as their first parameter."
  else
      message = "Normal methods should have at least one parameter (the first of which should be 'self')."
) and
not func instanceof ZopeInterfaceMethod

select f, message
