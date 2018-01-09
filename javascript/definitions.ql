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
 * @name Jump-to-definition links
 * @description Generates use-definition pairs that provide the data
 *              for jump-to-definition in the code viewer.
 * @kind definitions
 * @id js/jump-to-definition
 */

import javascript
private import Declarations.Declarations

/**
 * Gets the kind of reference that `va` represents.
 *
 * References in callee position have kind `"M"` (for "method"), all
 * others have kind `"V"` (for "variable").
 *
 * For example, in the expression `f(x)`, `f` has kind `"M"` while
 * `x` has kind `"V"`.
 */
string refKind(VarAccess va) {
  if exists(InvokeExpr invk | va = invk.getCallee().stripParens()) then
    result = "M"
  else
    result = "V"
}

/**
 * Holds if variable access `va` is of kind `kind` and refers to the
 * variable declaration.
 *
 * For example, in the statement `var x = 42, y = x;`, the initializing
 * expression of `y` is a variable access `x` of kind `"V"` that refers to
 * the declaration `x = 42`.
 */
predicate variableLookup(VarAccess va, VarDecl decl, string kind) {
  // restrict to declarations in same file to avoid accidentally picking up
  // unrelated global definitions
  decl = firstRefInTopLevel(va.getVariable(), Decl(), va.getTopLevel()) and
  kind = refKind(va)
}

/**
 * Holds if path expression `path`, which appears in a CommonJS `require`
 * call or an ES 2015 import statement, imports module `target`; `kind`
 * is always "I" (for "import").
 *
 * For example, in the statement `var a = require("./a")`, the path expression
 * `"./a"` imports a module `a` in the same folder.
 */
predicate importLookup(PathExpr path, Module target, string kind) {
  kind = "I" and
  target = any(Import i | path = i.getImportedPath()).getImportedModule()
}

from ASTNode ref, ASTNode decl, string kind
where variableLookup(ref, decl, kind) or
      importLookup(ref, decl, kind)
select ref, decl, kind
