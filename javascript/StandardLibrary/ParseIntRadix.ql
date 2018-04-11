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
 * @name Call to parseInt without radix
 * @description Calls to the 'parseInt' function should always specify a radix to avoid accidentally
 *              parsing a number as octal.
 * @kind problem
 * @problem.severity recommendation
 * @id js/parseint-without-radix
 * @tags reliability
 *       maintainability
 *       external/cwe/cwe-676
 * @precision very-high
 */

import javascript

from DataFlow::CallNode parseInt
where parseInt = DataFlow::globalVarRef("parseInt").getACall() and
      parseInt.getNumArgument() = 1
select parseInt, "Missing radix parameter."