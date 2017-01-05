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
 * @name Semicolon insertion
 * @description Code that relies on automatic semicolon insertion is hard to read and maintain.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       language-features
 */

import javascript
import semmle.javascript.RestrictedLocations

predicate asi(StmtContainer sc, Stmt s, boolean asi) {
    exists (TopLevel tl | tl = sc.getTopLevel() |
      not tl instanceof EventHandlerCode and
      not tl.isExterns()
    ) and
    sc = s.getContainer() and
    s.isSubjectToSemicolonInsertion() and
    (if s.hasSemicolonInserted() then asi = true else asi = false)
}

from Stmt s, StmtContainer sc, string sctype, float asi, int nstmt, int perc
where s.hasSemicolonInserted() and
      sc = s.getContainer() and
      (if sc instanceof Function then sctype = "function" else sctype = "script") and
      asi = strictcount(Stmt ss | asi(sc, ss, true)) and
      nstmt = strictcount(Stmt ss | asi(sc, ss, _)) and
      perc = ((1-asi/nstmt)*100).floor() and
      perc >= 90
select (LastLineOf)s, "Avoid automated semicolon insertion " +
                      "(" + perc + "% of all statements in $@ have an explicit semicolon).",
                      sc, "the enclosing " + sctype