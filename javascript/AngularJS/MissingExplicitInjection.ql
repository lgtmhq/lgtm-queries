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
 * @name Missing explicit dependency injection
 * @description Functions without explicit dependency injections
                will not work when their parameter names are minified.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/angular/missing-explicit-injection
 * @tags correctness
         maintainability
 *       frameworks/angularjs
 */

import javascript

from AngularJS::InjectableFunction f1, AngularJS::InjectableFunction f2
where f1.asFunction().getNumParameter() > 0 and
      not exists(f1.getAnExplicitDependencyInjection()) and
// ... but only if explicit dependencies are used somewhere else in the same file
      f1 != f2 and
      exists(f2.getAnExplicitDependencyInjection()) and
      f1.getLocation().getFile() = f2.getLocation().getFile()
select f1, "This function has no explicit dependency injections."
