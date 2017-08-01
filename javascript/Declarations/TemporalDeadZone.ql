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
 * @name Access to let-bound variable in temporal dead zone
 * @description Accessing a let-bound variable before its declaration will lead to a runtime
 *              error on ECMAScript 2015-compatible platforms.
 * @kind problem
 * @problem.severity error
 * @id js/variable-use-in-temporal-dead-zone
 * @tags portability
 *       correctness
 * @precision very-high
 */

import javascript

/**
 * Gets the (0-based) index among all statements in block `blk` at which
 * variable `v` is declared by statement `let`.
 */
int letDeclAt(BlockStmt blk, Variable v, LetStmt let) {
  let.getADecl().getBindingPattern().getAVariable() = v and
  let.getParentStmt*() = blk.getStmt(result)
}

from VarAccess va, LetStmt let, BlockStmt blk, int i, int j, Variable v
where v = va.getVariable() and
      j = letDeclAt(blk, v, let) and
      blk.getStmt(i) = va.getEnclosingStmt().getParentStmt*() and
      i < j and
      // don't flag uses in different functions
      blk.getContainer() = va.getContainer() and
      not letDeclAt(blk, v, _) < i
select va, "This expression refers to $@ inside its temporal dead zone.",  let, va.getName()
