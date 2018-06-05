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

import semmle.code.cpp.Element
import semmle.code.cpp.stmts.Stmt

/**
 * A C/C++ block statement. 
 *
 * For example,
 * ```
 * { int a; int b = 1; a = b; }
 * ```
 */
class Block extends Stmt, @stmt_block {

  /**
   * Gets a child declaration of this block.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; a = b; }
   * ```
   * it would have 2 results, for the declarations of `a` and `b`.
   */
  Declaration getADeclaration() {
    result = this.getAStmt().(DeclStmt).getADeclaration()
  }

  /**
   * Gets a body statement of this block.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; a = b; }
   * ```
   * it would have 3 results, for the declarations of `a` and `b` and
   * for the expression statement `a = b`.
   */
  Stmt getAStmt() { result = this.getAChild() }

  /**
   * Gets the `n`th body statement of this block, indexed from 0.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; a = b; }
   * ```
   * `getStmt(2)`'s result is the expression statement `a = b`.
   */
  Stmt getStmt(int n) { result = this.getChild(n) }
  
  /**
   * Gets the last body statement of this block.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; a = b; }
   * ```
   * the result is the expression statement `a = b`.
   */
  Stmt getLastStmt() { result = this.getStmt(this.getNumStmt()-1) }

  /**
   * Gets the last body statement of this block. If this last statement
   * is itself a block, returns the last statement of that block, and so on.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; { a = b; } }
   * ```
   * the result is the expression statement `a = b`.
   */
  Stmt getLastStmtIn() {
    if getLastStmt() instanceof Block then (
      result = getLastStmt().(Block).getLastStmtIn()
    ) else (
      result = getLastStmt()
    )
  }

  /**
   * Gets the number of body statements in this block.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; a = b; }
   * ```
   * the result is 3.
   */
  int getNumStmt() { result = count(this.getAStmt()) }
  
  /**
   * Holds if the block has no statements.
   * 
   * For example, the block 
   * ```
   * { }
   * ```
   * is empty, as is the block 
   * ```
   * {
   *   // a comment
   * }
   * ```
   */
  predicate isEmpty() { this.getNumStmt() = 0 }

  /**
   * Gets the index of the given statement within this block, indexed from 0.
   *
   * For example, for the block
   * ```
   * { int a; int b = 1; a = b; }
   * ```
   * if `s` is the expression statement `a = b` then `getIndexOfStmt(s)`
   * has result 2.
   */
  int getIndexOfStmt(Stmt s) { this.getStmt(result) = s }

  override string toString() { result = "{ ... }" }

  override predicate mayBeImpure() {
    this.getAStmt().mayBeImpure()
  }

  override predicate mayBeGloballyImpure() {
    this.getAStmt().mayBeGloballyImpure()
  }

}
