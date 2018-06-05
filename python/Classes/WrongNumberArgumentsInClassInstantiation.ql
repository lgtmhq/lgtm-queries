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
 * @name Wrong number of arguments in a class instantiation
 * @description Using too many or too few arguments in a call to the __init__
 *              method of a class will result in a TypeError at runtime.
 * @kind problem
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-685
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/call/wrong-number-class-arguments
 */

import python
import Expressions.CallArgs

from Call call, ClassObject cls, string too, string should, int limit, FunctionObject init
where
(
    too_many_args(call, cls, limit) and too = "too many arguments" and should = "no more than "
    or
    too_few_args(call, cls, limit) and too = "too few arguments" and should = "no fewer than "
) and init = get_function_or_initializer(cls)
select call, "Call to $@ with " + too + "; should be " + should + limit.toString() + ".", init, init.getQualifiedName()
