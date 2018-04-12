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
 * @name Unused AngularJS dependency
 * @description Unused dependencies are confusing, and should be removed.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id js/angular/unused-dependency
 * @tags maintainability
 *       frameworks/angularjs
 */

import javascript
import Declarations.UnusedParameter

predicate isUnusedParameter(Function f, string msg, Parameter parameter) {
  exists(Variable pv |
    isUnused(f, parameter, pv, _) and
    not isAnAccidentallyUnusedParameter(parameter) and // avoid double alerts
    msg = "Unused dependency " + pv.getName() + "."
  )
}

predicate isMissingParameter(AngularJS::InjectableFunction f, string msg, ASTNode location) {
    exists(int paramCount, int injectionCount |
    DataFlow::valueNode(location) = f and
    paramCount = f.asFunction().getNumParameter() and
    injectionCount = count(f.getADependencyDeclaration(_)) and
    paramCount < injectionCount and
    exists(string parametersString, string dependenciesAreString |
      (if paramCount = 1 then parametersString = "parameter" else parametersString = "parameters") and
      (if injectionCount = 1 then dependenciesAreString = "dependency is" else dependenciesAreString = "dependencies are") and
      msg = "This function has " + paramCount + " " + parametersString + ", but " + injectionCount + " " + dependenciesAreString + " injected into it."
    )
  )
}

from AngularJS::InjectableFunction f, string message, ASTNode location
where isUnusedParameter(f.asFunction(), message, location) or isMissingParameter(f, message, location)
select location, message
