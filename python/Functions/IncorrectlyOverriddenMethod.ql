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
 * @name Mismatch between signature and use of an overriding method
 * @description Method has a different signature from the overridden method and, if it were called, would be likely to cause an error.
 * @kind problem
 * @tags maintainability
 * @problem.severity error
 * @sub-severity low
 * @precision high
 * @id py/inheritance/incorrect-overriding-signature
 */

import python
import Expressions.CallArgs

from Call call, FunctionObject func, FunctionObject overridden, string problem
where
func.overrides(overridden) and (
    wrong_args(call, func, _, problem) and correct_args_if_called_as_method(call, overridden)
    or
    exists(string name | 
        illegally_named_parameter(call, func, name) and problem = "an argument named '" + name + "'" and
        overridden.getFunction().getAnArg().(Name).getId() = name
    )
)

select func, "Overriding method signature does not match $@, where it is passed " + problem + ". Overridden method $@ is correctly specified.",
call, "here", overridden, overridden.descriptiveString()
