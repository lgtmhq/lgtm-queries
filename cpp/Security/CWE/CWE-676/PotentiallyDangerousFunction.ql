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
 * @name Use of potentially dangerous function
 * @description Certain standard library functions are dangerous to call.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @tags reliability
 *       security
 *       external/cwe/cwe-676
 */
import cpp


predicate dangerousFunction(Function function) {
  exists (string name | name = function.getQualifiedName() |
    name = "gmtime")
}


from FunctionCall call, Function target
where call.getTarget() = target
  and dangerousFunction(target)
select call, "Call to " + target.getQualifiedName() + " is potentially dangerous"
