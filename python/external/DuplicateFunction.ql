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
 * @name Duplicate function
 * @description There is another identical implementation of this function. Extract the code to a common file or superclass to improve sharing.
 * @kind problem
 * @tags testability
 *       useless-code
 *       maintainability
 *       duplicate-code
 *       statistical
 * @problem.severity recommendation
 * @sub-severity high
 * @precision high
 * @id py/duplicate-function
 */
import python
import CodeDuplication

predicate relevant(Function m) {
    m.getMetrics().getNumberOfLinesOfCode() > 5
}

from Function m, Function other, string message, int percent
where duplicateScopes(m, other, percent, message)
  and relevant(m)
  and percent > 95.0
  and not duplicateScopes(m.getEnclosingModule(), other.getEnclosingModule(), _, _)
  and not duplicateScopes(m.getScope(), other.getScope(), _, _)
select m, message,
   other,
   other.getName()
