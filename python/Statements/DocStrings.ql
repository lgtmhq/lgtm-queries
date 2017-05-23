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
 * @name Missing docstring
 * @description Omitting documentation strings from public classes, functions or methods
 *              makes it more difficult for other developers to maintain the code.
 * @kind problem
 * @tags maintainability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 */

import python

predicate needs_docstring(Scope s) {
    s.isPublic() and
    (
      not s instanceof Function
      or
      function_needs_docstring(s)
    )
}

predicate function_needs_docstring(Function f) {
    not exists(FunctionObject fo, FunctionObject base | fo.overrides(base) and fo.getFunction() = f |
               not function_needs_docstring(base.getFunction())) and
    f.getName() != "lambda" and
    (f.getMetrics().getNumberOfLinesOfCode() - count(f.getADecorator())) > 2
    and not exists(PythonPropertyObject p | 
        p.getGetter().getFunction() = f or
        p.getSetter().getFunction() = f
    )
}

string scope_type(Scope s) {
    result = "Module" and s instanceof Module and not ((Module)s).isPackage()
    or
    result = "Class" and s instanceof Class
    or
    result = "Function" and s instanceof Function
}

from Scope s
where needs_docstring(s) and not exists(s.getDocString())
select s, scope_type(s) + " " + s.getName() + " does not have a docstring"


