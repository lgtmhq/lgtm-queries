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
 * @name Missing exports qualifier
 * @description Referencing an undeclared global variable in a module that exports
 *              a definition of the same name is confusing and may indicate a bug.
 * @kind problem
 * @problem.severity error
 * @id js/node/missing-exports-qualifier
 * @tags maintainability
 *       frameworks/node.js
 * @precision high
 */

import javascript

/** Holds if variable `v` is assigned somewhere in module `m`. */
predicate definedInModule(GlobalVariable v, NodeModule m) {
  exists (LValue def |
    def.getTopLevel() = m and
    def.(Expr).accessesGlobal(v.getName())
  )
}

from NodeModule m, GlobalVariable f, InvokeExpr invk, ASTNode export, GlobalVarAccess acc
where m.exports(f.getName(), export) and
      acc = f.getAnAccess() and
      invk.getCallee() = acc and
      invk.getTopLevel() = m and

      // don't flag if the variable is defined in the same module
      not definedInModule(f, m) and

      // don't flag if there is a linter directive declaring the variable
      not exists (Linting::GlobalDeclaration glob |
        glob.declaresGlobalForAccess(acc)
      ) and

      // don't flag if there is an externs declaration for the variable
      not exists (ExternalGlobalDecl egd | egd.getName() = f.getName()) and

      // don't flag if the invocation could refer to a property introduced by `with`
      not exists (WithStmt with | with.mayAffect(invk.getCallee()))
select invk, "'" + f.getName() + "' references an undeclared global variable, "
     + "not the variable exported $@.", export, "here"