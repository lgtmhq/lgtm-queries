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
 * @name Similar script
 * @description There is another script that shares a lot of code with this script.
 *              Extract the common parts to a new script to improve maintainability..
 * @kind problem
 * @problem.severity recommendation
 * @id js/similar-script
 * @tags testability
 *       maintainability
 *       useless-code
 *       statistical
 *       duplicate-code
 * @precision high
 */

import javascript
import CodeDuplication
import semmle.javascript.RestrictedLocations

from TopLevel one, TopLevel another, float percent
where similarContainers(one, another, percent) and
    one.getNumChildStmt() > 5 and
    not duplicateContainers(one, another, _)
select (FirstLineOf)one, percent.floor() + "% of statements in this script are similar to statements in $@.",
   (FirstLineOf)another,
   "another script"