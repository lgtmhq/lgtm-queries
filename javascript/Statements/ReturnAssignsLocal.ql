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
 * @name Return statement assigns local variable
 * @description An assignment to a local variable in a return statement is useless, since the variable will
 *              immediately go out of scope and its value is lost.
 * @kind problem
 * @problem.severity warning
 * @id js/useless-assignment-in-return
 * @tags maintainability
 *       readability
 *       external/cwe/cwe-563
 * @precision very-high
 */

import javascript
import semmle.javascript.RestrictedLocations

from ReturnStmt r, AssignExpr assgn, Variable v
where assgn = r.getExpr().stripParens() and
      v = ((Function)r.getContainer()).getScope().getAVariable() and
      not v.isCaptured() and
      assgn.getLhs() = v.getAnAccess()
select (FirstLineOf)r, "The assignment to " + v.getName() + " is useless, since it is a local variable and will go out of scope."