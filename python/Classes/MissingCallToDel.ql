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
 * @name Missing call to __del__ during object destruction 
 * @description An omitted call to a super-class __del__ method may lead to class instances not being cleaned up properly.
 * @kind problem
 * @problem.severity warning
 */

import python
import MethodCallOrder

predicate missing_call_to_del(ClassObject self, PyFunctionObject missing, ClassObject declarer) {
    declarer = self.getASuperType() and
    missing = declarer.declaredAttribute("__del__") and
    not missing = self.lookupAttribute("__del__") and
    not missing = next_function_in_chain(self, _) and
    not missing.neverReturns() and
    not self.failedInference()
}

from ClassObject self, FunctionObject missing, ClassObject declarer

where missing_call_to_del(self, missing, declarer) and
not missing_call_to_del(self.getABaseType(), missing, _)
select self, "Class " + self.getName() + " may not be cleaned up properly as $@ is not called during deletion.",
missing, missing.descriptiveString()
