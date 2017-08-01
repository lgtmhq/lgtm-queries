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
 * @name Conflicting variable initialization
 * @description If a variable is declared and initialized twice inside the same variable declaration
 *              statement, the second initialization immediately overwrites the first one.
 * @kind problem
 * @problem.severity error
 * @id js/variable-initialization-conflict
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-563
 * @precision very-high
 */

import javascript
import semmle.javascript.RestrictedLocations

from DeclStmt vds, VariableDeclarator vd1, VariableDeclarator vd2, int i, int j, Variable v
where vd1 = vds.getDecl(i) and
      vd2 = vds.getDecl(j) and
      v = vd1.getBindingPattern().getAVariable() and
      v = vd2.getBindingPattern().getAVariable() and
      i < j and
      // exclude a somewhat common pattern where the first declaration is used as a temporary
      exists (Expr e1, Expr e2 | e1 = vd1.getInit() and e2 = vd2.getInit() |
        not v.getAnAccess().getParentExpr*() = e2
      )
select (FirstLineOf)vd2, "This initialization of " + v.getName() + " overwrites $@.", vd1, "an earlier initialization"