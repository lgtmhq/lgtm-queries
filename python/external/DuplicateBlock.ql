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
 * @name Duplicate code block
 * @description This block of code is duplicated elsewhere. If possible, the shared code should be refactored so there is only one occurrence left. It may not always be possible to address these issues; other duplicate code checks (such as duplicate function, duplicate class) give subsets of the results with higher confidence.
 * @kind problem
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 * @id py/duplicate-block
 */
import CodeDuplication

predicate sorted_by_location(DuplicateBlock x, DuplicateBlock y) {
    if x.sourceFile() = y.sourceFile() then
        x.sourceStartLine() < y.sourceStartLine()
    else
        x.sourceFile().getName() < y.sourceFile().getName()
}

from DuplicateBlock d, DuplicateBlock other
where d.sourceLines() > 10 and
      other.getEquivalenceClass() = d.getEquivalenceClass() and
      sorted_by_location(other, d)
select 
   d, 
   "Duplicate code: " + d.sourceLines() + " lines are duplicated at " +
   other.sourceFile().getShortName() + ":" + other.sourceStartLine().toString()
