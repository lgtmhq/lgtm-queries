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
 * @name Multiple calls to __init__ during object initialization 
 * @description A duplicated call to a super-class __init__ method may lead to objects of this class not being properly initialized.
 * @kind problem
 * @problem.severity warning
 */

import python
import MethodCallOrder

predicate multiple_calls_to_method(ClassObject self, FunctionObject multi) {
    strictcount(FunctionObject x | multi = next_function_in_chain(self, x)) > 1
}

from ClassObject self, FunctionObject multi
where multi.getName() = "__init__" and
multiple_calls_to_method(self, multi) and
not multiple_calls_to_method(self.getABaseType(), multi) and
not self.failedInference()
select self, "Class " + self.getName() + " may not be initialized properly as $@ may be called multiple times during initialization.",
multi, multi.descriptiveString()
