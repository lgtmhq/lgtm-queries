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
 * @name Double compilation
 * @description Recompiling an already compiled part of the DOM can lead to
 *              unexpected behavior of directives, performance problems, and memory leaks.
 * @kind problem
 * @problem.severity warning
 * @id js/angular/double-compilation
 * @tags reliability
 *       frameworks/angularjs
 * @precision very-high
 */

import javascript

from AngularJS::ServiceReference compile, SimpleParameter elem, CallExpr c
where compile.getName() = "$compile" and
      elem = any(AngularJS::CustomDirective d).getALinkFunction().(AngularJS::LinkFunction).getElementParameter() and
      c = compile.getACall() and
      c.getArgument(0).(DataFlowNode).getALocalSource() = elem.getAnInitialUse() and
      // don't flag $compile calls that specify a `maxPriority`
      c.getNumArgument() < 3
select c, "This call to $compile may cause double compilation of '" + elem + "'."
