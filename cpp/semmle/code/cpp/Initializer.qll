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

import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A C/C++ declaration initializer.
 */
class Initializer extends @initialiser, ControlFlowNode {
  override Location getLocation() { initialisers(this,_,_,result) }

  /** Holds if this initializer is explicit in the source. */
  override predicate fromSource() {
    not (this.getLocation() instanceof UnknownLocation)
  }

  override string toString() {
    if exists(getDeclaration()) then (
      result = "initializer for " + max(getDeclaration().getName())
    ) else (
      result = "initializer"
    )
  }

  /** Gets the variable or enum constant being initialized. */
  Declaration getDeclaration() { initialisers(this,result,_,_) }

  /** Gets the initializing expression. */
  Expr getExpr() { initialisers(this,_,result,_) }

  /** Gets the function containing this control-flow node. */
  override Function getControlFlowScope() {
    result = this.getExpr().getEnclosingFunction()
  }

  override Stmt getEnclosingStmt() {
    result = this.getExpr().getEnclosingStmt()
  }
}
