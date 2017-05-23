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
 * @name Similar function
 * @description There is another function that is very similar this one. Extract the common code to a common function to improve sharing.
 * @kind problem
 * @tags testability
 *       maintainability
 *       useless-code
 *       duplicate-code
 *       statistical
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 */
import python
import CodeDuplication

predicate relevant(Function m) {
    m.getMetrics().getNumberOfLinesOfCode() > 10
}

from Function m, Function other, string message, int percent
where similarScopes(m, other, percent, message) and
    relevant(m) and
    percent > 95.0 and
    not duplicateScopes(m, other, _, _) and
    not duplicateScopes(m.getEnclosingModule(), other.getEnclosingModule(), _, _) and
    not duplicateScopes(m.getScope(), other.getScope(), _, _)
select m, message,
   other,
   other.getName()



