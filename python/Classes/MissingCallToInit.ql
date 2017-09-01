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
 * @name Missing call to __init__ during object initialization
 * @description An omitted call to a super-class __init__ method may lead to objects of this class not being fully initialized.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision high
 * @id py/missing-call-to-init
 */

import python
import MethodCallOrder

from ClassObject self, FunctionObject initializer, FunctionObject missing

where
    self.lookupAttribute("__init__") = initializer and
    missing_call_to_superclass_method(self, missing, "__init__") and
    // If a superclass is incorrect, don't flag this class as well.
    not missing_call_to_superclass_method(self.getASuperType(), missing, "__init__") and
    not missing = theObjectType().lookupAttribute("__init__") and
    not missing.neverReturns() and
    not self.failedInference() and
    not missing.isC()
select self, "Class " + self.getName() + " may not be initialized properly as $@ is not called from its $@.",
missing, missing.descriptiveString(), initializer, "__init__ method"