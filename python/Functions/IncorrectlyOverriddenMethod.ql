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
 */

import python
import Expressions.CallArgs

from Call call, FunctionObject func, FunctionObject overridden, string problem
where
overridden_call(overridden, func, call) and
(
    exists(int limit | too_many_args(call, func, limit) and problem = "too many arguments" and not too_many_args(call, overridden, limit))
    or
    exists(int limit | too_few_args(call, func, limit) and problem = "too few arguments" and not too_few_args(call, overridden, limit))
    or
    exists(string name | illegally_named_parameter(call, func, name) and problem = "an argument named '" + name + "'" and not illegally_named_parameter(call, overridden, name))
)
select func, "Overriding method signature does not match $@, where it is passed " + problem + ". Overridden method $@ is correctly specified.",
call, "here", overridden, overridden.descriptiveString()
