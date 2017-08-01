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
 * @name Assignment to constant
 * @description Assigning to a variable that is declared 'const' has either no effect or leads to a
 *              runtime error, depending on the platform.
 * @kind problem
 * @problem.severity error
 * @id js/assignment-to-constant
 * @tags reliability
 *       correctness
 * @precision very-high
 */

import javascript

from ConstDeclStmt cds, VariableDeclarator decl, VarDef def, Variable v
where decl = cds.getADecl() and
      def.getAVariable() = v and
      decl.getBindingPattern().getAVariable() = v and
      def != decl and
      def.(Expr).getTopLevel() = decl.getTopLevel()
select def, "Assignment to variable " + v.getName() + ", which is $@ constant.", cds, "declared"
