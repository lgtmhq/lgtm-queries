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
 * @name Wrong number of arguments in a call
 * @description A call to function may have an incorrect number of arguments. This will cause a TypeError to be raised.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/call/wrong-arguments
 */

import python
import CallArgs

from Call call, FunctionObject func, string too, string should, int limit
where
(
    too_many_args(call, func, limit) and too = "too many arguments" and should = "no more than "
    or
    too_few_args(call, func, limit) and too = "too few arguments" and should = "no fewer than "
) and
not func.isAbstract() and
not exists(FunctionObject overridden | func.overrides(overridden) and correct_args_if_called_as_method(call, overridden))
/* The semantics of `__new__` can be a bit subtle, so we simply exclude `__new__` methods */
and not func.getName() = "__new__"

select call, "Call to $@ with " + too + "; should be " + should + limit.toString() + ".", func, func.descriptiveString()

