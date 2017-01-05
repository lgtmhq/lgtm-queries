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
 * @problem.severity error
 * @tags reliability
 *       correctness
 */

import python
import Testing.Mox

int varargs_length(Call call) {
    not exists(call.getStarargs()) and result = 0
    or
    exists(TupleObject t |
        call.getStarargs().refersTo(t) |
        result = t.getLength()
    )
    or
    result = count(call.getStarargs().(List).getAnElt())
}

int positional_args(Call call) {
    result = count(call.getAnArg()) +
    varargs_length(call)
}

int kw_args(Call call) {
    result = count(call.getAKeyword())
}

int call_args(Call call) {
    result = positional_args(call) + kw_args(call)
}

int max_pcount(FunctionObject func) {
    result = max(int arg | exists(func.getFunction().getArg(arg))) + 1
    or
    result = 0 and not exists(func.getFunction().getAnArg()) and not func.isC()
}

int default_count(FunctionObject func) {
    result = count(Parameter p | p = func.getFunction().getAnArg() and exists(p.getDefault()))
}

int min_pcount(FunctionObject func) {
    result = max_pcount(func) - default_count(func) 
}

predicate too_few_args(Call call, FunctionObject func, int limit) {
    not exists(call.getStarargs()) and not exists(call.getKwargs()) and
    call_args(call) < limit and
    (call = func.getAFunctionCall().getNode() and limit = min_pcount(func) and
    /* The combination of misuse of `mox.Mox().StubOutWithMock()`
     * and a bug in mox's implementation of methods results in having to
     * pass 1 too few arguments to the mocked function.
     */
     not (useOfMoxInModule(call.getEnclosingModule()) and func.isNormalMethod())
     or
     call = func.getAMethodCall().getNode() and limit = min_pcount(func) - 1
    )
}

predicate too_many_args(Call call, FunctionObject func, int limit) {
    not func.getFunction().hasVarArg() and
    limit >= 0 and
    (call = func.getAFunctionCall().getNode() and limit = max_pcount(func)
     or
     call = func.getAMethodCall().getNode() and limit = max_pcount(func) - 1
    ) and
    (
        if func.getFunction().hasKwArg() then
            positional_args(call) > limit
        else  
            call_args(call) > limit
    )
}

from Call call, FunctionObject func, string too, string should, int limit
where
too_many_args(call, func, limit) and too = "Too many" and should = "no more than "
or
too_few_args(call, func, limit) and too = "Too few" and should = "no fewer than "

select call, too + " arguments in call to $@; should be " + should + limit.toString() + ".", func, func.descriptiveString()

