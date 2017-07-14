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
 * @name Variable not declared before use
 * @description Variables should be declared before their first use.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       readability
 * @precision very-high
 */

import javascript
private import Declarations

from VarAccess acc, VarDecl decl, Variable var, TopLevel tl
where // the first reference to `var` in `tl` is `acc` (that is, an access, not a declaration)
      acc = firstRefInTopLevel(var, Ref(), tl) and
      // `decl` is a declaration of `var` in `tl` (which must come after `acc`)
      decl = refInTopLevel(var, Decl(), tl) and
      // exclude function declarations
      not exists (FunctionDeclStmt f | f.getVariable() = var) and
      // exclude globals declared by a JSLint directive
      not exists(JSLintGlobal jslg | jslg.appliesTo(acc) | jslg.declaresGlobal(acc.getName(), _)) and
      // exclude declarations in synthetic constructors
      not acc.getEnclosingFunction() instanceof SyntheticConstructor
select acc, "Variable '" + acc.getName() + "' is used before its $@.", decl, "declaration"
