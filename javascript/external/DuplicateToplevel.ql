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
 * @name Duplicate script
 * @description There is another script that shares a lot of code with this script. Consider combining the
 *              two scripts to improve maintainability.
 * @kind problem
 * @problem.severity recommendation
 * @id js/duplicate-script
 * @tags testability
 *       maintainability
 *       useless-code
 *       statistical
 *       duplicate-code
 * @precision very-high
 */

import javascript
import CodeDuplication
import semmle.javascript.RestrictedLocations

from TopLevel one, TopLevel another, float percent
where duplicateContainers(one, another, percent) and
      one.getNumLines() > 5
select (FirstLineOf)one, percent + "% of statements in this script are duplicated in $@.", (FirstLineOf)another, "another script"
