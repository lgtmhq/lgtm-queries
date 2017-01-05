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
 * @name Typo in equals
 * @description A method named 'equal' may be intended to be named 'equals'.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       readability
 *       naming
 */
import java

from Method equal
where equal.hasName("equal") and 
      equal.getNumberOfParameters() = 1 and 
      equal.getAParamType() instanceof TypeObject and
      equal.fromSource()
select equal, "Did you mean to name this method 'equals' rather than 'equal'?"
