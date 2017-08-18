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
 * @name Mismatch between signature and use of an overridden method
 * @description Method has a signature that differs from both the signature of its overriding methods and
 *              the arguments with which it is called, and if it were called, would be likely to cause an error.
 * @kind problem
 * @tags maintainability
 * @problem.severity error
 * @sub-severity low
 * @precision high
 * @id py/inheritance/incorrect-overridden-signature
 */

import python
import Expressions.CallArgs

from Call call, FunctionObject func, FunctionObject overriding, string problem
where
// Exclude case where both base and derived are called as that is handled by by "wong name/number of arguments in call" query.
overridden_call(func, overriding, call) 
and
(
    exists(int limit | too_many_args(call, func, limit) and problem = "too many arguments" and not too_many_args(call, overriding, limit))
    or
    exists(int limit | too_few_args(call, func, limit) and problem = "too few arguments" and not too_few_args(call, overriding, limit))
    or
    exists(string name | illegally_named_parameter(call, func, name) | problem = "an argument named '" + name + "'" and not illegally_named_parameter(call, overriding, name))
)
select func, "Overridden method signature does not match $@, where it is passed " + problem + ". Overriding method $@ is matches the call.",
call, "call", overriding, overriding.descriptiveString()
