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
 * Static single assignment form.
 */

import javascript

/**
 * A data type representing SSA definitions.
 *
 * We distinguish three kinds of SSA definitions:
 *
 *   1. Explicit definitions wrapping a `VarDef` node in the CFG.
 *   2. Implicit initialisations of locals (including `arguments`) at
 *      the start of a function, which do not correspond directly to
 *      CFG nodes.
 *   3. Phi nodes.
 *
 * SSA definitions are only introduced where necessary. In particular,
 * unreachable code has no SSA definitions associated with it, and neither
 * have dead assignments (that is, assignments whose value is never read).
 */
newtype TSSADefinition =
     TExplicitDef(ReachableBasicBlock bb, int i, VarDef d, PurelyLocalVariable v) {
       bb.localLiveDefAt(v, i, d)
     }
  or TImplicitInit(EntryBasicBlock bb, PurelyLocalVariable v) {
       bb.localIsLiveAtEntry(v)
     }
  or TPhi(ReachableJoinBlock bb, PurelyLocalVariable v) {
       bb.localIsLiveAtEntry(v) and
       exists (ReachableBasicBlock defbb, SSADefinition def |
        def.assignsAt(defbb, _, v) and
        defbb.inDominanceFrontier(bb)
       )
     }

/**
 * An SSA definition.
 */
class SSADefinition extends TSSADefinition {
  /**
   * This SSA definition defines variable `v` at index `idx` in basic block `bb`.
   * Phi nodes, imports and implicit definitions are considered to be at index `-1`,
   * normal writes at the index of the CFG node they wrap.
   */
  abstract predicate assignsAt(ReachableBasicBlock bb, int idx, PurelyLocalVariable v);

  /** Get the variable defined by this definition. */
  abstract PurelyLocalVariable getVariable();

  /** Internal helper predicate for pretty-printing definitions. */
  abstract string prettyPrintDef();

  /** Internal helper predicate for pretty-printing references to definitions. */
  abstract string prettyPrintRef();

  string toString() { result = prettyPrintDef() }

  abstract predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec);

  /**
   * Get a use that refers to this definition.
   */
  VarUse getAUse() { this = getDefinition(getVariable(), result) }

  /** A definition that ultimately defines this variable and is not a phi node. */
  SSADefinition getAnUltimateDefinition() {
    result = getAPhiInput*(this) and
    not result instanceof SSAPhiNode
  }
}

/**
 * An SSA definition that corresponds to an explicit assignment or other variable definition.
 */
class SSAExplicitDefinition extends SSADefinition, TExplicitDef {
  predicate assignsAt(ReachableBasicBlock bb, int i, PurelyLocalVariable v) {
    this = TExplicitDef(bb, i, _, v)
  }

  /** This SSA definition corresponds to the definition of `v` at `def`. */
  predicate defines(VarDef d, PurelyLocalVariable v) {
    this = TExplicitDef(_, _, d, v)
  }

  /** The variable definition wrapped by this SSA definition. */
  VarDef getDef() {
    this = TExplicitDef(_, _, result, _)
  }

  PurelyLocalVariable getVariable() {
    this = TExplicitDef(_, _, _, result)
  }

  string prettyPrintRef() {
    exists (int l, int c | hasLocationInfo(_, l, c, _, _) |
      result = "def@" + l + ":" + c
    )
  }

  string prettyPrintDef() { result = getDef().toString() }

  predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
    getDef().getLocation().hasLocationInfo(filepath, bl, bc, el, ec)
  }
}

/**
 * An SSA definition that does not correspond to an explicit variable definition.
 */
abstract class SSAImplicitDefinition extends SSADefinition {
  /** Internal helper predicate used to implement prettyPrintRef. */
  abstract string getKind();

  /** The basic block to which this definition belongs. */
  abstract ReachableBasicBlock getBasicBlock();

  /** The variable updated by this definition. */
  abstract PurelyLocalVariable getVariable();

  predicate assignsAt(ReachableBasicBlock bb, int i, PurelyLocalVariable v) {
    bb = getBasicBlock() and v = getVariable() and i = -1
  }

  string prettyPrintRef() {
    exists (int l, int c | hasLocationInfo(_, l, c, _, _) |
      result = getKind() + "@" + l + ":" + c
    )
  }

  predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
    el = bl and ec = bc and
    getBasicBlock().getLocation().hasLocationInfo(filepath, bl, bc, _, _)
  }
}

/**
 * An SSA definition representing the implicit initialization of a variable
 * at the beginning of its scope.
 */
class SSAImplicitInit extends SSAImplicitDefinition, TImplicitInit {
  ReachableBasicBlock getBasicBlock() { this = TImplicitInit(result, _) }

  PurelyLocalVariable getVariable() { this = TImplicitInit(_, result) }

  string getKind() { result = "implicitInit" }

  string prettyPrintDef() {
    result = "implicit initialization of " + getVariable()
  }
}

/**
 * An SSA phi node, that is, a pseudo-definition for a variable at a point
 * in the flow graph where otherwise two or more definitions for the variable
 * would be visible.
 */
class SSAPhiNode extends SSAImplicitDefinition, TPhi {
  ReachableBasicBlock getBasicBlock() { this = TPhi(result, _) }

  PurelyLocalVariable getVariable() { this = TPhi(_, result) }

  string getKind() { result = "phi" }

  /** Get an input of this phi node. */
  SSADefinition getAnInput() {
    result = getAPhiInput(this)
  }

  string prettyPrintDef() {
    result = getVariable() + " = phi(" + ppInputs(1).suffix(2) + ")"
  }

  /** Helper predicate: get the i-th input in lexicographical order. */
  private SSADefinition getInput(int i) {
    result.prettyPrintRef() = rank[i](SSADefinition input |
      input = getAnInput() | input.prettyPrintRef()
    )
  }

  /** Helper predicate: pretty-print the inputs in lexicographical order. */
  private string ppInputs(int i) {
    result = ", " + getInput(i).prettyPrintRef() + ppInputs(i+1) or
    i = count(getAnInput())+1 and result = ""
  }

  predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
    el = bl and ec = bc and
    getBasicBlock().getLocation().hasLocationInfo(filepath, bl, bc, _, _)
  }
}

/** If `phi` is a phi node, the result is one of its inputs. */
private SSADefinition getAPhiInput(SSADefinition nd) {
  exists (SSAPhiNode phi | phi = nd |
    result = getDefReachingEndOf(phi.getVariable(),
                                 phi.getBasicBlock().getAPredecessor())
  )
}

/**
 * The (1-based) rank of the `i`-th node of `bb` among all SSA definitions
 * and uses of `v` in `bb`.
 *
 * For example, if `bb` is a basic block with a phi node for `v` (considered
 * to be at index -1), uses `v` at node 2 and defines it at node 5, we have:
 *
 * ```
 * defUseRank(bb, -1, v) = 1    // phi node
 * defUseRank(bb,  2, v) = 2    // use at node 2
 * defUseRank(bb,  5, v) = 3    // definition at node 5
 * ```
 */
private
int defUseRank(PurelyLocalVariable v, BasicBlock bb, int i) {
  i = rank[result](int j |
    any(SSADefinition ssa).assignsAt(bb, j, v) or
    bb.useAt(j, v, _)
  )
}

/**
 * The number of SSA definitions and uses of `v` in `bb`.
 */
private
int lastDefUseRank(PurelyLocalVariable v, BasicBlock bb) {
  result = max(defUseRank(v, bb, _))
}

/**
 * The (1-based) rank of `def` among all SSA definitions and uses of `v` in `bb`.
 */
private
int ssaDefRank(PurelyLocalVariable v, SSADefinition def, BasicBlock bb) {
  exists (int i | def.assignsAt(bb, i, v) | result = defUseRank(v, bb, i))
}

/**
 * The result is the unique SSA definition in `bb`, if it exists, whose value
 * reaches the `k`-th definition or use of `v` in `bb`.
 */
private
SSADefinition getLocalDefAt(PurelyLocalVariable v, ReachableBasicBlock bb, int k) {
  k = ssaDefRank(v, result, bb)
  or
  result = getLocalDefAt(v, bb, k-1) and k <= lastDefUseRank(v, bb) and
  not k = ssaDefRank(v, _, bb)
}

/**
 * The result is an SSA definition of `v` that reaches the end of basic block `bb`.
 */
private
SSADefinition getDefReachingEndOf(PurelyLocalVariable v, BasicBlock bb) {
  bb.getASuccessor().localIsLiveAtEntry(v) and
  (
    result = getLocalDefAt(v, bb, lastDefUseRank(v, bb))
    or
    /* In SSA form, the (unique) reaching definition of a use is the closest
     * definition that dominates the use. If two definitions dominate a node
     * then one must dominate the other, so we can find the reaching definition
     * by following the idominance relation backwards. */
    result = getDefReachingEndOf(v, bb.getImmediateDominator()) and
    not exists (SSADefinition ssa | ssa.assignsAt(bb, _, v))
  )
}

/**
 * The result is the unique SSA definition (if any) in the same block as `u`
 * whose value reaches `u`.
 */
private
SSADefinition getLocalDef(PurelyLocalVariable v, VarUse u) {
  exists (BasicBlock bb, int i |
    bb.useAt(i, v, u) and
    result = getLocalDefAt(v, bb, defUseRank(v, bb, i))
  )
}

/**
 * The result is the unique SSA definition whose value reaches the use `u`.
 */
private
SSADefinition getDefinition(PurelyLocalVariable v, VarUse u) {
  result = getLocalDef(v, u)
  or
  exists (BasicBlock bb | bb.useAt(_, v, u) |
    not exists(getLocalDef(v, u)) and
    result = getDefReachingEndOf(v, bb.getImmediateDominator())
  )
}