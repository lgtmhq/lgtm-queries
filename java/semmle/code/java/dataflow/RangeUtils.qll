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
 * Provides utility predicates for range analysis.
 */

import java
private import SSA
private import Guards

/** An expression that always has the same integer value. */
pragma[nomagic]
private predicate constantIntegerExpr(Expr e, int val) {
  e.(CompileTimeConstantExpr).getIntValue() = val or
  exists(SsaExplicitUpdate v, Expr src |
    e = v.getAUse() and
    src = v.getDefiningExpr().(VariableAssign).getSource() and
    constantIntegerExpr(src, val)
  )
}

/** An expression that always has the same integer value. */
class ConstantIntegerExpr extends Expr {
  ConstantIntegerExpr() {
    constantIntegerExpr(this, _)
  }

  /** Get the integer value of this expression. */
  int getIntValue() {
    constantIntegerExpr(this, result)
  }
}

/**
 * Gets an expression that equals `v - d`.
 */
Expr ssaRead(SsaVariable v, int delta) {
  result = v.getAUse() and delta = 0 or
  result.(ParExpr).getExpr() = ssaRead(v, delta) or
  exists(int d1, ConstantIntegerExpr c |
    result.(AddExpr).hasOperands(ssaRead(v, d1), c) and
    delta = d1 - c.getIntValue()
  ) or
  exists(SubExpr sub, int d1, ConstantIntegerExpr c |
    result = sub and
    sub.getLeftOperand() = ssaRead(v, d1) and
    sub.getRightOperand() = c and
    delta = d1 + c.getIntValue()
  ) or
  v.(SsaExplicitUpdate).getDefiningExpr().(PreIncExpr) = result and delta = 0 or
  v.(SsaExplicitUpdate).getDefiningExpr().(PreDecExpr) = result and delta = 0 or
  v.(SsaExplicitUpdate).getDefiningExpr().(PostIncExpr) = result and delta = 1 or  // x++ === ++x - 1
  v.(SsaExplicitUpdate).getDefiningExpr().(PostDecExpr) = result and delta = -1 or // x-- === --x + 1
  v.(SsaExplicitUpdate).getDefiningExpr().(Assignment) = result and delta = 0 or
  result.(AssignExpr).getSource() = ssaRead(v, delta)
}

/**
 * Holds if `inp` is an input to `phi` along the edge originating in `bb`.
 */
private predicate phiInputFromBlock(SsaPhiNode phi, SsaVariable inp, BasicBlock bb) {
  phi.getAPhiInput() = inp and
  phi.getBasicBlock().getABBPredecessor() = bb and
  inp.isLiveAtEndOfBlock(bb)
}

private newtype TSsaReadPosition =
  TSsaReadPositionBlock(BasicBlock bb) { exists(SsaVariable v | bb = v.getAUse().getBasicBlock()) } or
  TSsaReadPositionPhiInputEdge(BasicBlock bbOrig, BasicBlock bbPhi) {
    exists(SsaPhiNode phi | phiInputFromBlock(phi, _, bbOrig) and bbPhi = phi.getBasicBlock())
  }

/**
 * A position at which an SSA variable is read. This includes both ordinary
 * reads occurring in basic blocks and input to phi nodes occurring along an
 * edge between two basic blocks.
 */
class SsaReadPosition extends TSsaReadPosition {
  /** Holds if `v` is read at this position. */
  abstract predicate hasReadOfVar(SsaVariable v);

  abstract string toString();
}

/** A basic block in which an SSA variable is read. */
class SsaReadPositionBlock extends SsaReadPosition, TSsaReadPositionBlock {
  /** Gets the basic block corresponding to this position. */
  BasicBlock getBlock() { this = TSsaReadPositionBlock(result) }

  override predicate hasReadOfVar(SsaVariable v) { getBlock() = v.getAUse().getBasicBlock() }

  override string toString() { result = "block" }
}

/**
 * An edge between two basic blocks where the latter block has an SSA phi
 * definition. The edge therefore has a read of an SSA variable serving as the
 * input to the phi node.
 */
class SsaReadPositionPhiInputEdge extends SsaReadPosition, TSsaReadPositionPhiInputEdge {
  /** Gets the head of the edge. */
  BasicBlock getOrigBlock() { this = TSsaReadPositionPhiInputEdge(result, _) }

  /** Gets the tail of the edge. */
  BasicBlock getPhiBlock() { this = TSsaReadPositionPhiInputEdge(_, result) }

  override predicate hasReadOfVar(SsaVariable v) {
    exists(SsaPhiNode phi |
      phiInputFromBlock(phi, v, getOrigBlock()) and
      getPhiBlock() = phi.getBasicBlock()
    )
  }

  /** Holds if `inp` is an input to `phi` along this edge. */
  predicate phiInput(SsaPhiNode phi, SsaVariable inp) {
    phiInputFromBlock(phi, inp, getOrigBlock()) and
    getPhiBlock() = phi.getBasicBlock()
  }

  override string toString() { result = "edge" }
}

/**
 * Holds if the condition of `cb` controls the position `controlled` with the
 * value `testIsTrue`.
 */
predicate condControlsSsaRead(ConditionBlock cb, SsaReadPosition controlled, boolean testIsTrue) {
  cb.controls(controlled.(SsaReadPositionBlock).getBlock(), testIsTrue) or
  exists(SsaReadPositionPhiInputEdge controlledEdge | controlledEdge = controlled |
    cb.controls(controlledEdge.getOrigBlock(), testIsTrue) or
    cb = controlledEdge.getOrigBlock() and cb.getTestSuccessor(testIsTrue) = controlledEdge.getPhiBlock()
  )
}
