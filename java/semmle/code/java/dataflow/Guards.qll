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

import java
private import DefUse
private import semmle.code.java.controlflow.Dominance

/**
 * A basic block that terminates in a condition, splitting the subsequent control flow.
 */
class ConditionBlock extends BasicBlock {
  ConditionBlock() {
    this.getLastNode() instanceof ConditionNode
  }

  /** The last node of this basic block. */
  ConditionNode getConditionNode() {
    result = this.getLastNode()
  }

  /** The condition of the last node of this basic block. */
  Expr getCondition() {
    result = this.getConditionNode().getCondition()
  }

  /** A `true`- or `false`-successor of the last node of this basic block. */
  BasicBlock getTestSuccessor(boolean testIsTrue) {
    result = this.getConditionNode().getABranchSuccessor(testIsTrue)
  }
  
  /** Basic blocks controlled by this condition, that is, those basic blocks for which the condition is `testIsTrue`. */
  predicate controls(BasicBlock controlled, boolean testIsTrue) {
    /*
     * For this block to control the block `controlled` with `testIsTrue` the following must be true:
     * Execution must have passed through the test i.e. `this` must strictly dominate `controlled`.
     * Execution must have passed through the `testIsTrue` edge leaving `this`.
     * 
     * Although "passed through the true edge" implies that `this.getATrueSuccessor()` dominates `controlled`,
     * the reverse is not true, as flow may have passed through another edge to get to `this.getATrueSuccessor()`
     * so we need to assert that `this.getATrueSuccessor()` dominates `controlled` *and* that
     * all predecessors of `this.getATrueSuccessor()` are either `this` or dominated by `this.getATrueSuccessor()`.
     * 
     * For example, in the following java snippet:
     * ```
     * if (x)
     *   controlled;
     * false_successor;
     * uncontrolled;
     * ```
     * `false_successor` dominates `uncontrolled`, but not all of its predecessors are `this` (`if (x)`)
     *  or dominated by itself. Whereas in the following code:
     * ```
     * if (x)
     *   while (controlled)
     *     also_controlled;
     * false_successor;
     * uncontrolled;
     * ```
     * the block `while controlled` is controlled because all of its predecessors are `this` (`if (x)`)
     * or (in the case of `also_controlled`) dominated by itself.
     * 
     * The additional constraint on the predecessors of the test successor implies
     * that `this` strictly dominates `controlled` so that isn't necessary to check
     * directly.
     */
    exists(BasicBlock succ |
      succ = this.getTestSuccessor(testIsTrue) and
      succ.bbDominates(controlled) and
      forall(BasicBlock pred | pred = succ.getABBPredecessor() and pred != this |
        succ.bbDominates(pred)
      )
    )
  }
}

/** Holds if `n` updates the locally scoped variable `v`. */
predicate variableUpdate(ControlFlowNode n, LocalScopeVariable v) {
  exists(VariableUpdate a | a = n | a.getDestVar() = v)
}

/** Holds if `bb` updates the locally scoped variable `v`. */
private predicate variableUpdateBB(BasicBlock bb, LocalScopeVariable v) {
  variableUpdate(bb.getANode(), v)
}

/** Indicates the position of phi-nodes in an SSA representation. */
private predicate needPhiNode(BasicBlock bb, LocalScopeVariable v) {
  exists(BasicBlock def | dominanceFrontier(def, bb) |
    variableUpdateBB(def, v) or needPhiNode(def, v)
  )
}

/** Locally scoped variable `v` occurs in the condition of `cb`. */
private predicate relevantVar(ConditionBlock cb, LocalScopeVariable v) {
  v.getAnAccess() = cb.getCondition().getAChildExpr*()
}

/** Blocks controlled by the condition in `cb` for which `v` is unchanged. */
private predicate controlsBlockWithSameVar(ConditionBlock cb, boolean testIsTrue, LocalScopeVariable v, BasicBlock controlled) {
  cb.controls(controlled, testIsTrue) and
  relevantVar(cb, v) and
  not needPhiNode(controlled, v) and
  (
    controlled = cb.getTestSuccessor(testIsTrue)
    or
    exists(BasicBlock mid |
      controlsBlockWithSameVar(cb, testIsTrue, v, mid) and
      not variableUpdateBB(mid, v) and
      controlled = mid.getABBSuccessor()
    )
  )
}

/**
 * Statements controlled by the condition in `s` for which `v` is unchanged (`v` is the same SSA
 * variable in both `s` and `controlled`). The condition in `s` must contain an access of `v`.
 */
predicate controlsNodeWithSameVar(ConditionNode cn, boolean testIsTrue, LocalScopeVariable v, ControlFlowNode controlled) {
  exists(ConditionBlock cb, BasicBlock controlledBB, int i |
    cb.getConditionNode() = cn and
    controlsBlockWithSameVar(cb, testIsTrue, v, controlledBB) and
    controlled = controlledBB.getNode(i) and
    not exists(ControlFlowNode update, int j | update = controlledBB.getNode(j) and j < i and variableUpdate(update, v)))
}
