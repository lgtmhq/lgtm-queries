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
 * @name For-in loop with non-local iteration variable
 * @description For-in loops whose iteration variable is not a purely local variable may
 *              prevent optimization of the surrounding function.
 * @kind problem
 * @problem.severity warning
 * @tags efficiency
 *       maintainability
 */

import javascript

from ForInStmt f, string reason
where // exclude toplevel statements, since the toplevel is unlikely to be optimized anyway
      not f.getContainer() instanceof TopLevel and
      (f.getIterator() instanceof PropAccess and reason = "a property" or
       exists (Variable v | v = f.getAnIterationVariable() |
         v.isGlobal() and reason = "a global variable" or
         v.isLocal() and v.isCaptured() and reason = "captured"
       ))
select f.getIterator(), "This for-in loop may prevent optimization because its iteration variable is " + reason + "."