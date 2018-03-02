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
 * @name Block with too many statements
 * @description Blocks with too many consecutive statements are candidates for refactoring. Only complex statements are counted here (eg. for, while, switch ...). The top-level logic will be clearer if each complex statement is extracted to a function.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/complex-block
 * @tags testability
 *       readability
 *       maintainability
 */
import cpp

class ComplexStmt extends Stmt {
  ComplexStmt() {
    exists(Block body | body = this.(Loop      ).getStmt() or
                        body = this.(SwitchStmt).getStmt()
                      | strictcount(body.getAStmt+()) > 6)
    and not exists (this.getGeneratingMacro())
  }
}

from Block b, int n, ComplexStmt complexStmt
where n = strictcount(ComplexStmt s | s = b.getAStmt()) and n > 3
  and complexStmt = b.getAStmt()
select b, "Block with too many statements (" + n.toString() + " complex statements in the block). Complex statements at: $@", complexStmt, complexStmt.toString()

