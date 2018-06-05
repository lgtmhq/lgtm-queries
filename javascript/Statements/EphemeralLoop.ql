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
 * @name Loop body executes at most once
 * @description A loop that executes at most once is confusing and should be rewritten
 *              as a conditional.
 * @kind problem
 * @problem.severity recommendation
 * @id js/single-run-loop
 * @tags readability
 * @precision high
 */

import javascript
import semmle.javascript.RestrictedLocations
import semmle.javascript.frameworks.Emscripten

from LoopStmt l, BasicBlock body
where body = l.getBody().getBasicBlock() and
      not body.getASuccessor+() = body and
      not l instanceof EnhancedForLoop and
      // Emscripten generates lots of `do { ... } while(0);` loops, so exclude
      not l.getTopLevel() instanceof EmscriptenGeneratedToplevel
select (FirstLineOf)l, "This loop executes at most once."