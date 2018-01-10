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

import semmle.code.cpp.Variable

/**
 * A C/C++ variable which is used within the condition of a 'for' loop, and
 * mutated within the update expression of the same 'for' loop.
 */
class LoopCounter extends Variable {
  LoopCounter() {
    exists(ForStmt f | f.getAnIterationVariable() = this)
  }

  // Gets an access of this variable within loop `f`.
  VariableAccess getVariableAccessInLoop(ForStmt f) {
    this.getALoop() = f and
    result.getEnclosingStmt().getParent*() = f and
    this = result.getTarget()
  }

  // Gets a loop which uses this variable as its counter.
  ForStmt getALoop() {
    result.getAnIterationVariable() = this
  }
}

/**
 * A C/C++ variable which is used within the initialization, condition, or
 * update expression of a 'for' loop.
 */
class LoopControlVariable extends Variable {
  LoopControlVariable() {
    this = loopControlVariable(_)
  }

  // Gets an access of this variable within loop `f`.
  VariableAccess getVariableAccessInLoop(ForStmt f) {
    this.getALoop() = f and
    result.getEnclosingStmt().getParent*() = f and
    this = result.getTarget()
  }

  // Gets a loop which uses this variable as its control variable.
  ForStmt getALoop() {
    this = loopControlVariable(result)
  }
}

/**
 * Gets a control variable of loop `f`.
 */
private Variable loopControlVariable(ForStmt f) {
  exists(Expr e
  | result.getAnAccess().getParent*() = e
  | e = f.getControllingExpr() or
    e = f.getInitialization().(ExprStmt).getExpr() or
    e = f.getUpdate())
}
