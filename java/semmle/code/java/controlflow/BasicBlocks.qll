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
 * Provides classes and predicates for working with basic blocks in Java.
 */

import java
import Dominance
import semmle.code.java.ControlFlowGraph

/**
 * A control-flow node that represents the start of a basic block.
 *
 * A basic block is a series of nodes with no control-flow branching, which can
 * often be treated as a unit in analyses.
 */
class BasicBlock extends ControlFlowNode {
  BasicBlock() {
    not exists(this.getAPredecessor()) and exists(this.getASuccessor())
    or strictcount(this.getAPredecessor()) > 1
    or exists(ControlFlowNode pred | pred = this.getAPredecessor() | strictcount(pred.getASuccessor()) > 1)
  }

  /** Gets an immediate successor of this basic block. */
  cached
  BasicBlock getABBSuccessor() {
    result = getLastNode().getASuccessor()
  }

  /** Gets an immediate predecessor of this basic block. */
  BasicBlock getABBPredecessor() {
    result.getABBSuccessor() = this
  }

  /** Gets a control-flow node contained in this basic block. */
  ControlFlowNode getANode() { result = getNode(_) }

  /** Gets the control-flow node at a specific (zero-indexed) position in this basic block. */
  cached
  ControlFlowNode getNode(int pos) {
    result = this and pos = 0
    or
    exists(ControlFlowNode mid, int mid_pos | pos = mid_pos + 1 |
      getNode(mid_pos) = mid and
      mid.getASuccessor() = result and
      not result instanceof BasicBlock
    )
  }

  /** Gets the first control-flow node in this basic block. */
  ControlFlowNode getFirstNode() { result = this }

  /** Gets the last control-flow node in this basic block. */
  ControlFlowNode getLastNode() { result = getNode(length()-1) }

  /** Gets the number of control-flow nodes contained in this basic block. */
  cached
  int length() { result = strictcount(getANode()) }

  /** Holds if this basic block strictly dominates `node`. */
  predicate bbStrictlyDominates(BasicBlock node) { bbStrictlyDominates(this, node) }

  /** Holds if this basic block dominates `node`. (This is reflexive.) */
  predicate bbDominates(BasicBlock node) { bbDominates(this, node) }

  /** Holds if this basic block strictly post-dominates `node`. */
  predicate bbStrictlyPostDominates(BasicBlock node) { bbStrictlyPostDominates(this, node) }

  /** Holds if this basic block post-dominates `node`. (This is reflexive.) */
  predicate bbPostDominates(BasicBlock node) { bbPostDominates(this, node) }
}