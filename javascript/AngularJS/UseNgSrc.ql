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
 * @name Use of AngularJS markup in URL-valued attribute
 * @description Using AngularJS markup in an HTML attribute that references a URL
 *              (such as 'href' or 'src') may cause the browser to send a request
 *              with an invalid URL.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id js/angular/expression-in-url-attribute
 * @tags maintainability
 *       frameworks/angularjs
 */

import javascript

from HTML::Attribute attr, string name
where name = attr.getName() and
      // only flag URL-valued attributes...
      (name = "href" or name = "src" or name = "srcset") and
      // ...where the value contains some interpolated expressions
      attr.getValue().matches("%{{%}}") and
      // check that there is at least one use of an AngularJS attribute directive nearby
      // (`{{...}}` is used by other templating frameworks as well)
      any(AngularJS::DirectiveInstance d).getATarget().getElement().getRoot() = attr.getRoot()
select attr, "Use 'ng-" + name + "' instead of '" + name + "'."
