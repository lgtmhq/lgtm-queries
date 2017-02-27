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
 */

import python
import CallArgs

from Call call, FunctionObject func, string too, string should, int limit
where
(
    too_many_args(call, func, limit) and too = "Too many" and should = "no more than "
    or
    too_few_args(call, func, limit) and too = "Too few" and should = "no fewer than "
)
and
// Only report this as a fault of the call-site if all calls have the incorrect number of arguments.
forall(FunctionObject over |
    overridden_call(func, over, call) or overridden_call(over, func, call) |
    too_many_args(call, over, _) or too_few_args(call, over, _)
)

select call, too + " arguments in call to $@; should be " + should + limit.toString() + ".", func, func.descriptiveString()

