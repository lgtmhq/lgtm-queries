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
 * @name Jump from finally
 * @description Avoid using unstructured control flow statements (return, continue, or break) inside
 *              a 'finally' block.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       maintainability
 *       language-features
 *       external/cwe/cwe-584
 * @precision very-high
 */

import javascript

/**
 * A "jump" statement, that is, `break`, `continue` or `return`.
 */
class Jump extends Stmt {
  Jump() {
    this instanceof BreakOrContinueStmt or
    this instanceof ReturnStmt
  }

  /** Gets the target to which this jump refers. */
  Stmt getTarget() {
    result = ((BreakOrContinueStmt)this).getTarget() or
    result = ((Function)((ReturnStmt)this).getContainer()).getBody()
  }
}

from TryStmt try, BlockStmt finally, Jump jump
where finally = try.getFinally() and
      jump.getContainer() = try.getContainer() and
      jump.getParentStmt+() = finally and
      finally.getParentStmt+() = jump.getTarget()
select jump, "This statement jumps out of the finally block, potentially hiding an exception."