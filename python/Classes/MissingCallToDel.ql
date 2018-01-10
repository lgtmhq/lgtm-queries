// Copyright 2018 Semmle Ltd.
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
 * @tags efficiency
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision high
 * @id py/missing-call-to-delete
 */

import python
import MethodCallOrder


from ClassObject self, FunctionObject missing

where
    missing_call_to_superclass_method(self, missing, "__del__") and
    not missing.neverReturns() and
    not self.failedInference() and
    not missing.isBuiltin()
select self, "Class " + self.getName() + " may not be cleaned up properly as $@ is not called during deletion.",
missing, missing.descriptiveString()

