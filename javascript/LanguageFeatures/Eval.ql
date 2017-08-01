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
 * @name Use of eval
 * @description The 'eval' function and the 'Function' constructor execute strings as code. This is dangerous and impedes
 *              program analysis and understanding. Consequently, these two functions should not be used.
 * @kind problem
 * @problem.severity recommendation
 * @id js/eval-call
 * @tags maintainability
 *       language-features
 *       external/cwe/cwe-676
 * @precision very-high
 */

import javascript

/**
 * A call to `new Function(...)`.
 */
class NewFunction extends NewExpr {
  NewFunction() {
    accessesGlobal(this.getCallee(), "Function")
  }
}

/**
 * A call to `eval`.
 */
class EvalCall extends CallExpr {
  EvalCall() {
    accessesGlobal(this.getCallee(), "eval")
  }
}

/**
 * A call to `new Function(...)` or `eval`.
 */
class EvalUse extends InvokeExpr {
  EvalUse() {
    this instanceof NewFunction or this instanceof EvalCall
  }
}

from EvalUse eval
select eval, "Do not use eval or the Function constructor."