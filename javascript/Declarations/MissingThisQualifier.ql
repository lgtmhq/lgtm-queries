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
* @name Missing 'this' qualifier
* @description Referencing an undeclared global variable in a class that has a member of the same name is confusing and may indicate a bug.
* @kind problem
* @problem.severity error
* @id js/missing-this-qualifier
* @tags maintainability
*       correctness
*       methods
* @precision high
*/

import javascript

/**
 * Holds if `call` is a call to global function `gv` which has the same name as method
 * `intendedTarget` in the same class as `call`.
 */
predicate maybeMissingThis(CallExpr call, MethodDefinition intendedTarget, GlobalVariable gv) {
  call.getCallee() = gv.getAnAccess() and
  call.getCalleeName() = intendedTarget.getName() and
  exists(MethodDefinition caller |
    caller.getBody() = call.getContainer() and
    intendedTarget.getDeclaringClass() = caller.getDeclaringClass()
  )
}

from CallExpr call, MethodDefinition intendedTarget, GlobalVariable gv
where maybeMissingThis(call, intendedTarget, gv)
      and
      // exceptions:
      not (
        // affected by `with`
        exists (WithStmt with | with.mayAffect(call.getCallee()))
        or
        // locally declared, so probably intentional
        gv.getADeclaration().getTopLevel() = call.getTopLevel()
        or
        // linter declaration for the variable
        exists (Linting::GlobalDeclaration glob |
            glob.declaresGlobalForAccess(call.getCallee())
        )
        or
        // externs declaration for the variable
        exists (ExternalGlobalDecl egd | egd.getName() = call.getCalleeName())
      )
select call, "This call refers to a global function, and not the local method $@.", intendedTarget, intendedTarget.getName()
