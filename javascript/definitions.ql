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
 * @name Jump-to-definition links
 * @description Generates use-definition pairs that provide the data
 *              for jump-to-definition in the code viewer.
 * @kind definitions
 */

import javascript

/**
 * References in callee position have kind "M" (for "method"), all
 * others have kind "V" (for "variable").
 */
string refKind(VarAccess va) {
  if exists(InvokeExpr invk | va = invk.getCallee().stripParens()) then
    result = "M"
  else
    result = "V"
}

/**
 * Variable lookup: connect variable accesses to their declarations.
 */
predicate variableLookup(VarAccess va, VarDecl decl, string kind) {
  decl = va.getVariable().getADeclaration() and
  // restrict to same file to avoid accidentally picking up unrelated global definitions
  va.getFile() = decl.getFile() and
  kind = refKind(va)
}

/**
 * Import resolution: connect path expressions in Node.js require statements
 * and ES6 imports to the module they refer to.
 *
 * Kind is always "I" (for "import").
 */
predicate importLookup(PathExpr path, Module target, string kind) {
  kind = "I" and
  (
    exists (Require req | path = req.getImportedPath() |
      target = req.getImportedModule()
    )
    or
    exists (ImportDeclaration imp | path = imp.getImportedPath() |
      target = imp.getImportedModule()
    )
  )
}

from ASTNode ref, ASTNode decl, string kind
where variableLookup(ref, decl, kind) or
      importLookup(ref, decl, kind)
select ref, decl, kind
