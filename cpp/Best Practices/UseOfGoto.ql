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
 * @name Use of goto
 * @description The goto statement can make the control flow of a function hard
 *              to understand, when used for purposes other than error handling.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/use-of-goto
 * @tags maintainability
 *       readability
 *       language-features
 */

import cpp

class JumpTarget extends Stmt {
    JumpTarget() {
        exists(GotoStmt g | g.getTarget() = this)
    }

    FunctionDeclarationEntry getFDE() {
        result.getBlock() = this.getParentStmt+()
    }

    predicate isForward() {
        exists(GotoStmt g | g.getTarget() = this | g.getLocation().getEndLine() < this.getLocation().getStartLine())
    }

    predicate isBackward() {
        exists(GotoStmt g | g.getTarget() = this | this.getLocation().getEndLine() < g.getLocation().getStartLine())
    }
}

from FunctionDeclarationEntry fde, int nforward, int nbackward
where nforward =  strictcount(JumpTarget t | t.getFDE() = fde and t.isForward())
  and nbackward = strictcount(JumpTarget t | t.getFDE() = fde and t.isBackward())
  and nforward != 1
  and nbackward != 1
select fde, "Multiple forward and backward goto statements may make function "
            + fde.getName() + " hard to understand."
