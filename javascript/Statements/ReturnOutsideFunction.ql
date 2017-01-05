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
 * @name Return statement outside function
 * @description A 'return' statement appearing outside a function will cause an error
 *              when it is executed.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 */

import javascript
import semmle.javascript.RestrictedLocations

from ReturnStmt ret, TopLevel tl
where tl = ret.getContainer() and
      not tl instanceof EventHandlerCode and
      not tl instanceof NodeModule
select (FirstLineOf)ret, "Return statement outside function."