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
 * @name Call to eval-like DOM function
 * @description DOM functions that act like 'eval' and execute strings as code are dangerous and impede
 *              program analysis and understanding. Consequently, they should not be used.
 * @kind problem
 * @problem.severity recommendation
 * @id js/eval-like-call
 * @tags maintainability
 *       external/cwe/cwe-676
 * @precision very-high
 */

import javascript

/**
 * A call to either `setTimeout` or `setInterval` where
 * a string literal is passed as first argument.
 */
class EvilTwin extends CallExpr {
  EvilTwin() {
    exists (Expr callee | callee = this.getCallee() |
      accessesGlobal(callee, "setTimeout") or
      accessesGlobal(callee, "setInterval")
    ) and
    getArgument(0) instanceof StringLiteral
  }
}

/** A call to `document.write` or `document.writeln`. */
class DocumentWrite extends CallExpr {
  DocumentWrite() {
    exists (DotExpr callee | callee = this.getCallee() |
      accessesGlobal(callee.getBase(), "document") and
      callee.getPropertyName().regexpMatch("write(ln)?")
    )
  }
}

/** A call to `window.execScript`. */
class ExecScript extends CallExpr {
  ExecScript() {
    accessesGlobal(this.getCallee(), "execScript")
  }
}

/** A call to a DOM function that may evaluate a string as code. */
class PseudoEval extends CallExpr {
  PseudoEval() {
    this instanceof EvilTwin or
    this instanceof DocumentWrite or
    this instanceof ExecScript
  }
}

from PseudoEval pe
select pe, "Avoid using functions that evaluate strings as code."