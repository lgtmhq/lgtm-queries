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
 * @name Duplicate dependency
 * @description Repeated dependency names are redundant for AngularJS dependency injection.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id js/angular/duplicate-dependency
 * @tags maintainability
 *       frameworks/angularjs
 */

import javascript

predicate isRepeatedDependency(AngularJS::InjectableFunction f, string name, ASTNode location) {
  exists(int i, int j | i < j and
    exists(f.getDependencyDeclaration(i, name)) and
    location = f.getDependencyDeclaration(j, name)
  )
}
from AngularJS::InjectableFunction f, ASTNode node, string name
where isRepeatedDependency(f, name, node) and
      not count(f.asFunction().getParameterByName(name)) > 1 // avoid duplicating reports from js/duplicate-parameter-name
select f, "This function has a duplicate dependency '$@'.", node, name
