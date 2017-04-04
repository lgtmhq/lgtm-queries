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
 * Provides classes for working with basic blocks, and predicates for computing
 * liveness information for local variables.
 */

import CFG
import DefUse

/**
 * Holds if `nd` starts a new basic block.
 */
private predicate startsBB(ControlFlowNode nd) {
  (not exists(nd.getAPredecessor()) and exists(nd.getASuccessor())) or
  nd.isJoin() or
  exists (ControlFlowNode pred | pred = nd.getAPredecessor() |
    pred.isBranch() or
    // `yield` expressions always end their basic block to simplify
    // SSA conversion; see discussion in SSA.qll
    pred instanceof YieldExpr
  )
}

/**
 * Holds if `succ` is a control flow successor of `nd` within the same basic block.
 */
private predicate intraBBSucc(ControlFlowNode nd, ControlFlowNode succ) {
  succ = nd.getASuccessor() and
  not succ instanceof BasicBlock
}

/**
 * Holds if `nd` is the `i`th node in basic block `bb`.
 *
 * In other words, `i` is the shortest distance from a node `bb`
 * that starts a basic block to `nd` along the `intraBBSucc` relation.
 */
private cached predicate bbIndex(BasicBlock bb, ControlFlowNode nd, int i) =
  shortestDistances(startsBB/1, intraBBSucc/2)(bb, nd, i)

/**
 * Holds if the first node of basic block `succ` is a control flow
 * successor of the last node of basic block `bb`.
 */
private predicate succBB(BasicBlock bb, BasicBlock succ) {
  succ = bb.getLastNode().getASuccessor()
}

/** Holds if `bb` is an entry basic block. */
private predicate entryBB(BasicBlock bb) {
  bb.getFirstNode() instanceof ControlFlowEntryNode
}

/** Holds if `dom` is an immediate dominator of `bb`. */
private cached predicate bbIDominates(BasicBlock dom, BasicBlock bb) =
  idominance(entryBB/1, succBB/2)(_, dom, bb)

/**
 * A basic block, that is, a maximal straight-line sequence of control flow nodes
 * without branches or joins.
 *
 * At the database level, a basic block is represented by its first control flow node.
 */
class BasicBlock extends @cfg_node, Locatable {
  BasicBlock() {
    startsBB(this)
  }

  /** Gets a basic block succeeding this one. */
  BasicBlock getASuccessor() {
    succBB(this, result)
  }

  /** Gets a basic block preceding this one. */
  BasicBlock getAPredecessor() {
    result.getASuccessor() = this
  }

  /** Gets a node in this block. */
  ControlFlowNode getANode() { result = getNode(_) }

  /** Gets the node at the given position in this block. */
  ControlFlowNode getNode(int pos) {
    bbIndex(this, result, pos)
  }

  /** Gets the first node in this block. */
  ControlFlowNode getFirstNode() { result = this }

  /** Gets the last node in this block. */
  ControlFlowNode getLastNode() { result = getNode(length()-1) }

  /** Gets the length of this block. */
  int length() { result = strictcount(getANode()) }

  /** Holds if this basic block uses variable `v` in its `i`th node `u`. */
  predicate useAt(int i, Variable v, VarUse u) {
    v = u.getVariable() and u = this.getNode(i)
  }

  /** Holds if this basic block defines variable `v` in its `i`th node `u`. */
  predicate defAt(int i, Variable v, VarDef d) {
    v = d.getAVariable() and d = this.getNode(i)
  }

  /**
   * Holds if `v` is live at entry to this basic block and `u` is a use of `v`
   * witnessing the liveness.
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
   * Holds if `v` is live at entry to this basic block and `u` is a use of `v`
   * witnessing the liveness, where `v` is defined at least once in the enclosing
   * function or script.
   */
  private predicate isLiveAtEntryImpl(Variable v, VarUse u) {
    isLocallyLiveAtEntry(v, u)
    or
    isDefinedInSameContainer(v) and
    not this.defAt(_, v, _) and
    getASuccessor().isLiveAtEntryImpl(v, u)
  }

  /**
   * Holds if `v` is defined at least once in the function or script to which
   * this basic block belongs.
   */
  private predicate isDefinedInSameContainer(Variable v) {
    exists (VarDef def | def.getAVariable() = v and def.getContainer() = getContainer())
  }

  /**
   * Holds if `v` is a variable that is live at entry to this basic block.
   *
   * Note that this is equivalent to `bb.isLiveAtEntry(v, _)`, but may
   * be more efficient on large databases.
   */
  predicate isLiveAtEntry(Variable v) {
    isLocallyLiveAtEntry(v, _) or
    (not this.defAt(_, v, _) and getASuccessor().isLiveAtEntry(v))
  }

  /**
   * Holds if local variable `v` is live at entry to this basic block and
   * `u` is a use of `v` witnessing the liveness.
   */
  predicate localIsLiveAtEntry(LocalVariable v, VarUse u) {
    isLocallyLiveAtEntry(v, u) or
    (not this.defAt(_, v, _) and getASuccessor().localIsLiveAtEntry(v, u))
  }

  /**
   * Holds if local variable `v` is live at entry to this basic block.
   */
  predicate localIsLiveAtEntry(LocalVariable v) {
    isLocallyLiveAtEntry(v, _) or
    (not this.defAt(_, v, _) and getASuccessor().localIsLiveAtEntry(v))
  }

  /**
   * Holds if `d` is a definition of `v` that is reachable from the beginning of
   * this basic block without going through a redefinition of `v`.
   */
  predicate localMayBeOverwritten(LocalVariable v, VarDef d) {
    isLocallyOverwritten(v, d) or
    (not defAt(_, v, _) and getASuccessor().localMayBeOverwritten(v, d))
  }

  /**
   * Gets the next index after `i` in this basic block at which `v` is
   * defined or used, provided that `d` is a definition of `v` at index `i`.
   * If there are no further uses or definitions of `v` after `i`, the
   * result is the length of this basic block.
   */
  private int nextDefOrUseAfter(PurelyLocalVariable v, int i, VarDef d) {
    defAt(i, v, d) and
    result = min(int j | (defAt(j, v, _) or useAt(j, v, _) or j = length()) and j > i)
  }

  /**
   * Holds if `d` defines variable `v` at the `i`th node of this basic block, and
   * the definition is live, that is, the variable may be read after this
   * definition and before a re-definition.
   */
  predicate localLiveDefAt(PurelyLocalVariable v, int i, VarDef d) {
    exists (int j | j = nextDefOrUseAfter(v, i, d) |
      useAt(j, v, _) or
      j = length() and getASuccessor().localIsLiveAtEntry(v)
    )
  }

  /**
   * Holds if `u` is a use of `v` in this basic block, and there are
   * no definitions of `v` before it.
   */
  private predicate isLocallyLiveAtEntry(Variable v, VarUse u) {
    exists (int n | useAt(n, v, u) |
      not exists (int m | m < n | defAt(m, v, _))
    )
  }

  /**
   * Holds if `d` is a definition of `v` in this basic block, and there are
   * no other definitions of `v` before it.
   */
  private predicate isLocallyOverwritten(Variable v, VarDef d) {
    exists (int n | defAt(n, v, d) |
      not exists (int m | m < n | defAt(m, v, _))
    )
  }

  /**
   * Gets the function or script to which this basic block belongs.
   */
  StmtContainer getContainer() {
    result = getFirstNode().getContainer()
  }

  /**
   * Gets the basic block that immediately dominates this basic block.
   */
  ReachableBasicBlock getImmediateDominator() {
    bbIDominates(result, this)
  }
}

/**
 * An unreachable basic block, that is, a basic block
 * whose first node is unreachable.
 */
class UnreachableBlock extends BasicBlock {
  UnreachableBlock() { getFirstNode().isUnreachable() }
}

/**
 * An entry basic block, that is, a basic block
 * whose first node is the entry node of a statement container.
 */
class EntryBasicBlock extends BasicBlock {
  EntryBasicBlock() { entryBB(this) }
}

/**
 * A basic block that is reachable from an entry basic block.
 */
class ReachableBasicBlock extends BasicBlock {
  ReachableBasicBlock() {
    this instanceof EntryBasicBlock or
    this.getAPredecessor() instanceof ReachableBasicBlock
  }

  /**
   * Holds if this basic block strictly dominates `bb`.
   */
  cached
  predicate strictlyDominates(ReachableBasicBlock bb) {
    bbIDominates+(this, bb)
  }

  /**
   * Holds if this basic block dominates `bb`.
   *
   * This predicate is reflexive: each reachable basic block dominates itself.
   */
  predicate dominates(ReachableBasicBlock bb) {
    bb = this or
    strictlyDominates(bb)
  }

  /**
   * Holds if `df` is in the dominance frontier of this basic block, that is,
   * this basic block dominates a predecessor of `df`, but not `df` itself.
   */
  predicate inDominanceFrontier(ReachableJoinBlock df) {
    dominatesPredecessor(df) and
    not strictlyDominates(df)
  }

  /**
   * Holds if this basic block dominates a predecessor of `df`.
   */
  private
  predicate dominatesPredecessor(ReachableJoinBlock df) {
    exists (BasicBlock pred | pred = df.getAPredecessor() |
      this = pred or
      strictlyDominates(pred)
    )
  }
}

/**
 * A reachable basic block with more than one predecessor.
 */
class ReachableJoinBlock extends ReachableBasicBlock {
  ReachableJoinBlock() { getFirstNode().isJoin() }
}
