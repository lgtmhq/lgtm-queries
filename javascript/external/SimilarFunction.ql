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
 * @name Similar function
 * @description There is another function that shares a lot of code with this function.
 *              Extract the common parts to a shared utility function to improve maintainability.
 * @kind problem
 * @problem.severity recommendation
 * @id js/similar-function
 * @tags testability
 *       maintainability
 *       useless-code
 *       statistical
 *       non-attributable
 *       duplicate-code
 * @precision very-high
 */

import javascript
import CodeDuplication
import semmle.javascript.RestrictedLocations

from Function f, Function g, float percent
where similarContainers(f, g, percent) and
      f.getNumBodyStmt() > 5 and
      not duplicateContainers(f, g, _) and
      not duplicateContainers(f.getEnclosingStmt().getContainer(), g.getEnclosingStmt().getContainer(), _)
select (FirstLineOf)f, percent.floor() + "% of statements in " + f.describe() +
   " are similar to statements in $@.", (FirstLineOf)g, g.describe()
