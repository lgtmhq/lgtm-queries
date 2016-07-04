// Copyright 2016 Semmle Ltd.
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
 * @name Duplicate switch case
 * @description If two cases in a switch statement have the same label, the second case
 *              will never be executed.
 * @kind problem
 * @problem.severity warning
 */

import Clones

class DuplicateSwitchCase extends StructurallyCompared {
  DuplicateSwitchCase() {
    exists (Case c | this = c.getExpr())
  }

  Expr candidate() {
    exists (SwitchStmt s, int i, int j |
      this = s.getCase(i).getExpr() and
      result = s.getCase(j).getExpr() and
      i < j
    )
  }
}

from DuplicateSwitchCase e, Expr f
where e.same(f)
select f, "This case label is a duplicate of $@.", e, e.toString()
