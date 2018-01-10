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
 * @name Dependency mismatch
 * @description If the injected dependencies of a function go out of sync
 *              with its parameters, the function will become difficult to
 *              understand and maintain.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id js/angular/dependency-injection-mismatch
 * @tags correctness
 *       maintainability
 *       frameworks/angularjs
 */

import javascript

from AngularJS::InjectableFunction f, SimpleParameter p, string msg
where p = f.asFunction().getAParameter() and
      (
        not p = f.getDependencyParameter(_) and
        msg = "This parameter has no injected dependency."
        or
        exists (string n | p = f.getDependencyParameter(n) |
          p.getName() != n and
          exists(f.getDependencyParameter(p.getName())) and
          msg = "This parameter is named '" + p.getName() + "', " +
                "but actually refers to dependency '" + n + "'."
        )
      )
select p, msg