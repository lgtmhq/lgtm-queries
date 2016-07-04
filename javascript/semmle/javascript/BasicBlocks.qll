// Copyright 2016 Semmle Ltd.
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

/*
 * Basic blocks and liveness analysis for local variables.
 */

import CFG
import DefUse

/**
 * A basic block, that is, a maximal straight-line sequence of control flow nodes
 * without branches or joins.
 *
 * <p>
 * At the database level, a basic block is represented by its first control flow node.
 * </p>
 */
class BasicBlock extends @cfg_node, Locatable {
  BasicBlock() {
    exists (CFGNode nd | nd = this |
      (not exists(nd.getAPredecessor()) and exists(nd.getASuccessor())) or
      nd.isJoin() or
      nd.getAPredecessor().isBranch()
    )
  }
  
  /** Get a basic block succeeding this one. */
  cached
  BasicBlock getASuccessor() {
    result = getLastNode().getASuccessor()
  }
  
  /** Get a basic block preceding this one. */
  BasicBlock getAPredecessor() {
    result.getASuccessor() = this
  }
  
  /** Get a node in this block. */
  CFGNode getANode() { result = getNode(_) }
  
  /** Get the node at the given position in this block. */
  cached
  CFGNode getNode(int pos) {
    result = this and pos = 0
    or
    exists(int mid_pos | pos = mid_pos + 1 | 
      result = getNode(mid_pos).getASuccessor() and
      not result instanceof BasicBlock
    )
  }
  
  /** Get the first node in this block. */
  CFGNode getFirstNode() { result = this }
  
  /** Get the last node in this block. */
  CFGNode getLastNode() { result = getNode(length()-1) }

  /** The length of this block */
  cached
  int length() { result = strictcount(getANode()) }

  /** Does this basic block use variable `v` in its `i`-th node `u`? */
  predicate useAt(int i, Variable v, VarUse u) {
    v = u.getVariable() and u = this.getNode(i)
  }

  /** Does this basic block define variable `v` in its `i`-th node `u`? */
  predicate defAt(int i, Variable v, VarDef d) {
    v = d.getAVariable() and d = this.getNode(i)
  }

  /**
   * Bind `v` to variables that are live at entry to this basic block,
   * where `u` is a use of `v` witnessing the liveness.
   *
   * In other words, `u` is a use of `v` that is reachable from the
   * entry node of this basic block without going through a redefinition
   * of `v`. The use `u` may either be in this basic block, or in another
   * basic block reachable from this one.
   */
  predicate isLiveAtEntry(Variable v, VarUse u) {
    // restrict `u` to be reachable from this basic block
    u = getASuccessor*().getANode() and
    (// shortcut: if `v` is never defined, then it must be live
     isDefinedInSameContainer(v) implies
     // otherwise, do full liveness computation
     isLiveAtEntryImpl(v, u))
  }

  /**
   * Implementation of liveness analysis; requires `v` to be
   * defined at least once in the enclosing function or script.
   */
  private predicate isLiveAtEntryImpl(Variable v, VarUse u) {
    isLocallyLiveAtEntry(v, u) or
    (isDefinedInSameContainer(v) and not this.defAt(_, v, _) and getASuccessor().isLiveAtEntryImpl(v, u))
  }

  /**
   * Is `v` defined at least once in the function or script to which
   * this basic block belongs?
   */
  private predicate isDefinedInSameContainer(Variable v) {
    exists (VarDef def | def.getAVariable() = v and def.(Expr).getContainer() = getContainer())
  }

  /**
   * Bind `v` to variables that are live at entry to this basic block.
   *
   * Note that this is equivalent to `bb.isLiveAtEntry(v, _)`, but may
   * be more efficient on large snapshots.
   */
  predicate isLiveAtEntry(Variable v) {
    isLocallyLiveAtEntry(v, _) or
    (not this.defAt(_, v, _) and getASuccessor().isLiveAtEntry(v))
  }

  /**
   * Alternative implementation of `isLiveAtEntry` for purely local variables.
   */
  predicate localIsLiveAtEntry(PurelyLocalVariable v, VarUse u) {
    isLocallyLiveAtEntry(v, u) or
    (not this.defAt(_, v, _) and getASuccessor().localIsLiveAtEntry(v, u))
  }

  /**
   * Bind `v` to purely local variables that are live at entry to this basic block.
   */
  predicate localIsLiveAtEntry(PurelyLocalVariable v) {
    isLocallyLiveAtEntry(v, _) or
    (not this.defAt(_, v, _) and getASuccessor().localIsLiveAtEntry(v))
  }

  /**
   * Bind `d` to definitions of `v` that are reachable from the beginning of
   * this basic block without going through a redefinition of `v`.
   */
  predicate localMayBeOverwritten(PurelyLocalVariable v, VarDef d) {
    isLocallyOverwritten(v, d) or
    (not this.defAt(_, v, _) and getASuccessor().localMayBeOverwritten(v, d))
  }

  private predicate isLocallyLiveAtEntry(Variable v, VarUse u) {
    exists (int n | useAt(n, v, u) |
      not exists (int m | m < n | defAt(m, v, _))
    )
  }

  private predicate isLocallyOverwritten(Variable v, VarDef d) {
    exists (int n | defAt(n, v, d) |
      not exists (int m | m < n | defAt(m, v, _))
    )
  }

  /**
   * Get the function or script to which this basic block belongs.
   */
  StmtContainer getContainer() {
    this = result.getEntry() or this = result.getExit() or
    result = this.(Expr).getContainer() or
    result = this.(Stmt).getContainer() or
    result = this.(Property).getContainer() or
    result = this.(PropertyPattern).getContainer()
  }
}
