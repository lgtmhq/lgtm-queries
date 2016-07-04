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
 * @name 'exec' used
 * @description The 'exec' statement or function is used which could cause arbitrary code to be executed.
 * @kind problem
 * @problem.severity warning
 */

import python

string message() {
    result = "The 'exec' statement is used." and major_version() = 2
    or
    result = "The 'exec' function is used." and major_version() = 3
}

predicate exec_function_call(Call c) {
	major_version() = 3 and exists(GlobalVariable exec | exec = ((Name)c.getFunc()).getVariable() and exec.getId() = "exec")
}

from AstNode exec
where exec_function_call(exec) or exec instanceof Exec
select exec, message()
