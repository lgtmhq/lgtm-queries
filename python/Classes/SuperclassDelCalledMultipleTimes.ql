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
 * @name Multiple calls to __del__ during object destruction
 * @description A duplicated call to a super-class __del__ method may lead to class instances not be cleaned up properly.
 * @kind problem
 * @problem.severity warning
 * @tags efficiency
 *       correctness
 */

import python
import MethodCallOrder

from ClassObject self, FunctionObject multi
where 
multiple_calls_to_superclass_method(self, multi, "__del__") and
not multiple_calls_to_superclass_method(self.getABaseType(), multi, "__del__") and
not self.failedInference()
select self, "Class " + self.getName() + " may not be cleaned up properly as $@ may be called multiple times during destruction.",
multi, multi.descriptiveString()
