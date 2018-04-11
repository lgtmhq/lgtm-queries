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
 * @name Function with too many parameters
 * @description Functions with many parameters are hard to read and hard to use.
 * @kind problem
 * @problem.severity recommendation
 * @id js/too-many-parameters
 * @tags testability
 *       readability
 * @precision high
 */

import javascript
import semmle.javascript.RestrictedLocations

from Function f
where not f.inExternsFile() and
      f.getNumParameter() > 7 and
      // exclude AMD modules
      not exists (AMDModuleDefinition m | f = m.getFactoryNode().(DataFlow::FunctionNode).getAstNode())
select (FirstLineOf)f, capitalize(f.describe()) + " has too many parameters (" + f.getNumParameter() + ")."