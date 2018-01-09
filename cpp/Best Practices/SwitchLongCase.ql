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
 * @name Long switch case
 * @description A switch statement with too much code in its cases can make the control flow hard to follow. Consider wrapping the code for each case in a function and just using the switch statement to invoke the appropriate function in each case.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/long-switch
 * @tags maintainability
 *       readability
 */
import default

predicate switchCaseStartLine(SwitchCase sc, int start) {
  sc.getLocation().getStartLine() = start
}
predicate switchStmtEndLine(SwitchStmt s, int start) {
  s.getLocation().getEndLine() = start
}

predicate switchCaseLength(SwitchCase sc, int length) {
  exists(SwitchCase next, int l1, int l2 |
    next = sc.getNextSwitchCase() and
    switchCaseStartLine(next, l1) and
    switchCaseStartLine(sc, l2) and
    length = l1 - l2 - 1
  )
  or
  (
    not exists(sc.getNextSwitchCase()) and
    exists(int l1, int l2 |
      switchStmtEndLine(sc.getSwitchStmt(), l1) and
      switchCaseStartLine(sc, l2) and
      length = l1 - l2 - 1
    )
  )
}

predicate tooLong(SwitchCase sc) {
  exists(int n | switchCaseLength(sc, n) and n > 30)
}

from SwitchStmt switch, SwitchCase sc, int lines
where sc = switch.getASwitchCase() and tooLong(sc)
  and switchCaseLength(sc, lines)
select switch, "Switch has at least one case that is too long: $@", sc, sc.getExpr().toString() + " (" + lines.toString() + " lines)"
