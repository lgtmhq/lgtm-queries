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
 * @name Signature mismatch in overriding method
 * @description Overriding a method without ensuring that both methods accept the same
 *              number and type of parameters has the potential to cause an error when there is a mismatch.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 * @problem.severity warning
 * @sub-severity high
 * @precision very-high
 * @id py/inheritance/signature-mismatch
 */

import python
import Expressions.CallArgs

from FunctionObject base, PyFunctionObject derived
where
  // Exclude case where both base and derived are called as that is handled by by "wong name/number of arguments in call" query.
  not overridden_call(base, derived, _) and
  derived.getName() != "__init__" and
  derived.isNormalMethod() and
  not derived.getFunction().isSpecialMethod() and
  // call to overrides distributed for efficiency
  (
    (derived.overrides(base) and derived.minParameters() > base.maxParameters())
    or
    (derived.overrides(base) and derived.maxParameters() < base.minParameters())
  )
select derived, "Overriding method '" + derived.getName() + "' has signature mismatch with $@.", base, "overridden method"
