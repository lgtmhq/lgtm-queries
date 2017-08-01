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
 * @name Redeclared variable
 * @description Declaring the same variable twice is confusing and may even suggest a latent bug.
 * @kind problem
 * @problem.severity recommendation
 * @id js/variable-redeclaration
 * @tags reliability
 *       readability
 * @precision very-high
 */

import javascript
private import Declarations

from Variable v, TopLevel tl, VarDecl decl, VarDecl redecl
where decl = firstRefInTopLevel(v, Decl(), tl) and
      redecl = refInTopLevel(v, Decl(), tl) and
      redecl != decl and
      not tl.isExterns()
select redecl, "This variable has already been declared $@.", decl, "here"