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
 * @name Signature mismatch in overriding method
 * @description Overriding a method without ensuring that both methods accept the same
 *  number and type of parameters causes an error when there is a mismatch.
 * @kind problem
 * @problem.severity error
 */

import python

predicate method_parameter_counts(FunctionObject func, int min_parameter_count, int max_parameter_count) {
    func.getName() != "__init__" and
    func.isNormalMethod() and
    min_parameter_count = func.minParameters() and
    max_parameter_count = func.maxParameters()
}

predicate liskov_violation(FunctionObject base, FunctionObject derived, boolean strict) {
  derived.overrides(base) and
  exists(int base_min, int base_max, int derived_min, int derived_max |
    method_parameter_counts(base, base_min, base_max) and
    method_parameter_counts(derived, derived_min, derived_max) and
    (strict = true and (derived_min > base_min or derived_max < base_max)
	   or
     strict = false and (derived_min > base_max or derived_max < base_min)))
}

from FunctionObject base, PyFunctionObject derived
where 
    not derived.getFunction().isSpecialMethod() and
    liskov_violation(base, derived, false)
select derived, "Overriding method '" + derived.getName() + "' has signature mismatch with $@.", base, "overridden method"
