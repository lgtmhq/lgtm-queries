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
 * @name Misleading indentation after control statement
 * @description The body of a control statement should have appropriate indentation to clarify which
 *              statements it controls and which ones it does not control.
 * @kind problem
 * @problem.severity warning
 * @tags changeability
 *       correctness
 */

import javascript
import semmle.javascript.RestrictedLocations

/**
 * Statement `s1` is controlled by `ctrl`, and is immediately followed by `s2`, which is not;
 * hence `s2` should be less indented than `s1`.
 *
 * We ignore the case where `s1` is not indented relative to `ctrl` in the first place.
 */
predicate shouldOutdent(ControlStmt ctrl, Stmt s1, Stmt s2) {
  s1.getLastToken().getNextToken() = s2.getFirstToken() and
  s1 = ctrl.getAControlledStmt() and
  s1.getLocation().getStartColumn() > ctrl.getLocation().getStartColumn() and
  not s2 = ctrl.getAControlledStmt()
}

/** Statement `s2` should be indented less than `s1`, but has in fact the same indentation. */
predicate missingOutdent(Stmt s1, Stmt s2) {
  shouldOutdent(_, s1, s2) and
  s1.getLocation().getStartColumn() = s2.getLocation().getStartColumn() and
  s1.getStartLine().getIndentChar() = s2.getStartLine().getIndentChar()
}

from ControlStmt ctrl, Stmt s1, Stmt s2
where shouldOutdent(ctrl, s1, s2) and
      missingOutdent(s1, s2) and
      not ctrl.getTopLevel().isMinified()
select (FirstLineOf)s2, "The indentation of this statement suggests that it is controlled by $@, while in fact it is not.",
            (FirstLineOf)ctrl, "this statement"