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
 * @name Unread local variable
 * @description A local variable that is never read is redundant.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/local-variable-is-never-read
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-561
 */

import java

VarAccess getARead(LocalVariableDecl v) {
  v.getAnAccess() = result and
  not exists(Assignment assign | assign.getDest() = result)
}

predicate readImplicitly(LocalVariableDecl v) {
  exists(TryStmt t | t.getAResourceDecl().getAVariable() = v.getDeclExpr())
}

from LocalVariableDecl v
where not exists(getARead(v))
  // Discarded exceptions are covered by another query.
  and not exists(CatchClause cc | cc.getVariable().getVariable() = v)
  and not readImplicitly(v)
select v, "Variable '" + v + "' is never read."
