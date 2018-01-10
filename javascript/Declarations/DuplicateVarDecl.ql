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
 * @name Duplicate variable declaration
 * @description A variable declaration statement that declares the same variable twice is
 *              confusing and hard to maintain.
 * @kind problem
 * @problem.severity recommendation
 * @id js/duplicate-variable-declaration
 * @tags maintainability
 * @precision very-high
 */

import javascript

from DeclStmt vds, VariableDeclarator vd1, int i, VariableDeclarator vd2, int j, Variable v
where vd1 = vds.getDecl(i) and
      vd2 = vds.getDecl(j) and
      vd1.getBindingPattern().getAVariable() = v and
      vd2.getBindingPattern().getAVariable() = v and
      i < j
select vd2, "Variable " + v.getName() + " has already been declared $@.", vd1, "here"