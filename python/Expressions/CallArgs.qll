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

import python

import Testing.Mox

private int varargs_length(Call call) {
    not exists(call.getStarargs()) and result = 0
    or
    exists(TupleObject t |
        call.getStarargs().refersTo(t) |
        result = t.getLength()
    )
    or
    result = count(call.getStarargs().(List).getAnElt())
}

/** Gets a keyword argument that is not a keyword-only parameter. */
private Keyword not_keyword_only_arg(Call call, FunctionObject func) {
    func.getACall().getNode() = call and
    result = call.getAKeyword() and
    not func.getFunction().getAKeywordOnlyArg().getId() = result.getArg()
}

/** Gets the count of arguments that are passed as positional parameters even if they
 *  are named in the call.
 *  This is the sum of the number of positional arguments, the number of elements in any explicit tuple passed as *arg
 *  plus the number of keyword arguments that do not match keyword-only arguments (if the function does not take **kwargs).
 */
private int positional_arg_count_for_call(Call call, FunctionObject func) {
    call = func.getACall().getNode() and
    exists(int positonal_keywords |
        not func.getFunction().hasKwArg() and positonal_keywords = count(not_keyword_only_arg(call, func))
        or
        func.getFunction().hasKwArg() and positonal_keywords = 0
        |
        result = count(call.getAnArg()) + varargs_length(call) + positonal_keywords
    )
}

int arg_count(Call call) {
    result = count(call.getAnArg()) + varargs_length(call) + count(call.getAKeyword())
}

/**Whether there are too few arguments in the `call` to `func` where `limit` is the lowest number of legal arguments */
predicate illegally_named_parameter(Call call, FunctionObject func, string name) {
    not func.isC() and
    name = call.getANamedArgumentName() and
    call.getAFlowNode() = func.getACall() and
    not func.isLegalArgumentName(name)
}

predicate too_few_args(Call call, FunctionObject func, int limit) {
    // Exclude cases where an incorrect name is used as that is covered by 'Wrong name for an argument in a call'
    not illegally_named_parameter(call, func, _) and
    not exists(call.getStarargs()) and not exists(call.getKwargs()) and
    arg_count(call) < limit and
    (call = func.getAFunctionCall().getNode() and limit = func.minParameters() and
    /* The combination of misuse of `mox.Mox().StubOutWithMock()`
     * and a bug in mox's implementation of methods results in having to
     * pass 1 too few arguments to the mocked function.
     */
     not (useOfMoxInModule(call.getEnclosingModule()) and func.isNormalMethod())
     or
     call = func.getAMethodCall().getNode() and limit = func.minParameters() - 1
    )
}

/**Whether there are too many arguments in the `call` to `func` where `limit` is the highest number of legal arguments */
predicate too_many_args(Call call, FunctionObject func, int limit) {
    // Exclude cases where an incorrect name is used as that is covered by 'Wrong name for an argument in a call'
    not illegally_named_parameter(call, func, _) and
    not func.getFunction().hasVarArg() and
    limit >= 0 and
    (call = func.getAFunctionCall().getNode() and limit = func.maxParameters()
     or
     call = func.getAMethodCall().getNode() and limit = func.maxParameters() - 1
    ) and
    positional_arg_count_for_call(call, func) > limit
}

/** Holds if `call` has too many or too few arguments for `func` */
predicate wrong_args(Call call, FunctionObject func, int limit, string too) {
    too_few_args(call, func, limit) and too = "too few"
    or
    too_many_args(call, func, limit) and too = "too many"
}

/** Holds if `call` has correct number of arguments for `func`.
 * Implies nothing about whether `call` could call `func`.
 */
 bindingset[call, func]
predicate correct_args_if_called_as_method(Call call, FunctionObject func) {
    arg_count(call)+1 >= func.minParameters()
    and
    arg_count(call) < func.maxParameters()
}

/** Holds if `call` is a call to `overriding`, which overrides `func`. */
predicate overridden_call(FunctionObject func, FunctionObject overriding, Call call)  {
    overriding.overrides(func) and
    overriding.getACall().getNode() = call
}
