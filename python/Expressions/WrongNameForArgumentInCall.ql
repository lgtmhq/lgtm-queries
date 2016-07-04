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
 * @name Wrong name for an argument in a call
 * @description A call to function may name an argument for a parameter that does not exist. This will cause a TypeError to be raised.
 * @kind problem
 * @problem.severity error
 */

import python

string name_in_explicit_dict(Call call) {
    result = call.getKwargs().(Dict).getAKey().(StrConst).getText()
}

predicate illegal_name_parameter(Call call, FunctionObject func, string name) {
    not func.isC() and
    not func.getFunction().hasKwArg() and
    (call.getAKeyword().getArg() = name or name = name_in_explicit_dict(call)) and 
    call.getAFlowNode() = func.getACall() and
    not func.getFunction().getAnArg().asName().getId() = name and
    not func.getFunction().getAKeywordOnlyArg().getId() = name
}


from Call call, FunctionObject func, string name
where
illegal_name_parameter(call, func, name)
select
call, "Keyword argument '" + name + "' is not a supported parameter name of $@.", func, func.descriptiveString()
