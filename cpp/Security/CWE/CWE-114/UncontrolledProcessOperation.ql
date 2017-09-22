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
 * @name Uncontrolled process operation
 * @description Using externally controlled strings in a process
 *              operation can allow an attacker to execute malicious
 *              commands.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags security
 *       external/cwe/cwe-114
 */

import cpp
import semmle.code.cpp.security.Security
import semmle.code.cpp.security.TaintTracking

from string processOperation, int processOperationArg,
     FunctionCall call, Expr arg, Element source
where isProcessOperationArgument(processOperation, processOperationArg)
  and call.getTarget().getName() = processOperation
  and call.getArgument(processOperationArg) = arg
  and tainted(source, arg)
select arg,
  "The value of this argument may come from $@ and is being passed to " + processOperation,
  source, source.toString()
