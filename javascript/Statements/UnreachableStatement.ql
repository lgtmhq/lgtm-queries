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
 * @name Unreachable statement
 * @description Unreachable statements are often indicative of missing code or latent bugs and should be avoided.
 * @kind problem
 * @problem.severity warning
 * @id js/unreachable-statement
 * @tags maintainability
 *       correctness
 *       external/cwe/cwe-561
 * @precision very-high
 */

import javascript
import semmle.javascript.RestrictedLocations

from Stmt s
where // `s` is unreachable in the CFG
      s.getFirstControlFlowNode().isUnreachable() and
      // the CFG does not model all possible exceptional control flow, so be conservative about catch clauses
      not s instanceof CatchClause and
      // function declarations are special and always reachable
      not s instanceof FunctionDeclStmt and
      // allow a spurious 'break' statement at the end of a switch-case
      not exists(Case c, int i | i = c.getNumBodyStmt() | (BreakStmt)s = c.getBodyStmt(i-1)) and
      // ignore ambient statements
      not s.isAmbient()
select (FirstLineOf)s, "This statement is unreachable."