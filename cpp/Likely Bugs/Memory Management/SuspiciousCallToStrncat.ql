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
 * @name Potentially unsafe call to strncat
 * @description Calling 'strncat' with the size of the destination buffer
 *              as the third argument may result in a buffer overflow.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/unsafe-strncat
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-676
 *       external/cwe/cwe-119
 *       external/cwe/cwe-251
 */
import cpp
import Buffer

from FunctionCall fc, VariableAccess va1, VariableAccess va2
where fc.getTarget().(Function).hasName("strncat") and
      va1 = fc.getArgument(0) and
      va2 = fc.getArgument(2).(BufferSizeExpr).getArg() and
      va1.getTarget() = va2.getTarget()
select fc, "Potentially unsafe call to strncat."
