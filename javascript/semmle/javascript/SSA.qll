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
 * Provides classes for working with static single assignment form (SSA).
 *
 * We compute SSA form based on the intra-procedural CFG, without
 * any call graph information. Hence we can only deal with _trackable_
 * variables, which are local variables that are only assigned to within
 * the function that declares them, but not within any nested functions
 * that capture them.
 *
 * Such variables can be treated as purely local within their
 * declaring function, since any assignments to the variable must
 * be within that function.
 *
 * Within each nested function `f` that accesses a captured variable
 * `x`, we introduce a pseudo-assignment to `x` called a _capture of `x`
 * at the beginning of the function that (conceptually) captures
 * the current value of `x`.
 *
 * Additionally, if `f` is a generator containing a `yield` expression,
 * we insert similar pseudo-assignments to `x` after each `yield`
 * expression that re-captures the current value of `x`. This is
 * necessary because, in general, the `yield` might transfer control
 * back to the declaring function of `x` which might update `x`.
 *
 * For example, consider the following function:
 *
 * ```
 * function k() {
 *   var x = 0;
 *
 *   function* iter() {
 *     console.log(x);
 *     yield;
 *     console.log(x);
 *   }
 *
 *   var gen = iter();
 *   gen.next();
 *   ++x;
 *   gen.next();
 * }
 * ```
 *
 * Here, `x` is trackable (since it is only assigned within `k`),
 * so `iter` has a pseudo-assignment for `x` at its beginning.
 * Additionally, there is a pseudo-assignment after the `yield`,
 * which reflects the fact that `x` is incremented between the
 * two `console.log` calls.
 *
 * Note that a `yield` always ends its enclosing basic block,
 * so captures (like phi nodes) only occur at the beginning
 * of a basic block.
 */

import javascript
private import semmle.javascript.flow.Refinements

/**
 * A variable that is trackable for purposes of SSA conversion,
 * meaning that all its definitions appear in the container inside
 * which it is declared.
 */
class TrackableVariable extends LocalVariable {
  TrackableVariable() {
    exists (StmtContainer sc | sc = getDeclaringContainer() |
      forall (LValue def | def = getAnAccess() |
        def.getContainer() = sc
      )
    )
  }
}

/**
 * A data type representing SSA definitions.
 *
 * We distinguish five kinds of SSA definitions:
 *
 *   1. Explicit definitions wrapping a `VarDef` node in the CFG.
 *   2. Implicit initialisations of locals (including `arguments`) at
 *      the start of a function, which do not correspond directly to
 *      CFG nodes.
 *   3. Pseudo-definitions for captured variables at the beginning of
 *      the capturing function as well as after `yield` expressions.
 *   4. Phi nodes.
 *   5. Refinement nodes at points in the CFG where additional information
 *      about a variable becomes available, which may constrain the set of
 *      its potential values.
 *
 * SSA definitions are only introduced where necessary. In particular,
 * unreachable code has no SSA definitions associated with it, and neither
 * have dead assignments (that is, assignments whose value is never read).
 */
newtype TSSADefinition =
     TExplicitDef(ReachableBasicBlock bb, int i, VarDef d, TrackableVariable v) {
       bb.defAt(i, v, d) and not v instanceof PurelyLocalVariable or
       bb.localLiveDefAt(v, i, d)
     }
  or TImplicitInit(EntryBasicBlock bb, TrackableVariable v) {
       bb.getContainer() = v.getDeclaringContainer() and
       bb.localIsLiveAtEntry(v)
     }
  or TCapture(ReachableBasicBlock bb, TrackableVariable v) {
       bb.getContainer() != v.getDeclaringContainer() and
       exists (ControlFlowNode fst | fst = bb.getFirstNode() |
         fst instanceof ControlFlowEntryNode or
         fst.getAPredecessor() instanceof YieldExpr
       ) and
       bb.localIsLiveAtEntry(v)
     }
  or TPhi(ReachableJoinBlock bb, TrackableVariable v) {
       bb.localIsLiveAtEntry(v) and
       exists (ReachableBasicBlock defbb, SSADefinition def |
        def.assignsAt(defbb, _, v) and
        defbb.inDominanceFrontier(bb)
       )
     }
  or TRefinement(ReachableBasicBlock bb, GuardControlFlowNode guard, TrackableVariable v) {
       bb.getNode(0) = guard and
       guard.getTest().(Refinement).getRefinedVar() = v and
       bb.localIsLiveAtEntry(v)
     }

/**
 * An SSA definition.
 */
class SSADefinition extends TSSADefinition {
  /**
   * Holds if this SSA definition defines variable `v` at index `idx` in basic block `bb`.
   *
   * Phi nodes, imports and implicit definitions are considered to be at index `-1`,
   * normal writes at the index of the CFG node they wrap.
   */
  abstract predicate assignsAt(ReachableBasicBlock bb, int idx, TrackableVariable v);

  /** Gets the variable defined by this definition. */
  abstract TrackableVariable getVariable();

  /**
   * INTERNAL: Use `toString()` instead.
   *
   * Gets a pretty-printed representation of this SSA definition.
   */
  abstract string prettyPrintDef();

  /**
   * INTERNAL: Do not use.
   *
   * Gets a pretty-printed representation of a reference to this SSA definition.
   */
  abstract string prettyPrintRef();

  /** Gets a textual representation of this element. */
  string toString() { result = prettyPrintDef() }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/docs/ql/locations).
   */
  abstract predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                     int endline, int endcolumn);

  /**
   * Gets a use that refers to this definition.
   */
  VarUse getAUse() { this = getDefinition(getVariable(), result) }

  /**
   * Gets a definition that ultimately defines this variable and is not a pseudo definition.
   */
  SSADefinition getAnUltimateDefinition() {
    result = getAPseudoDefinitionInput*(this) and
    not result instanceof SSAPhiNode and
    not result instanceof SSARefinement
  }
}

/**
 * An SSA definition that corresponds to an explicit assignment or other variable definition.
 */
class SSAExplicitDefinition extends SSADefinition, TExplicitDef {
  override predicate assignsAt(ReachableBasicBlock bb, int i, TrackableVariable v) {
    this = TExplicitDef(bb, i, _, v)
  }

  /** This SSA definition corresponds to the definition of `v` at `def`. */
  predicate defines(VarDef d, TrackableVariable v) {
    this = TExplicitDef(_, _, d, v)
  }

  /** The variable definition wrapped by this SSA definition. */
  VarDef getDef() {
    this = TExplicitDef(_, _, result, _)
  }

  override TrackableVariable getVariable() {
    this = TExplicitDef(_, _, _, result)
  }

  override string prettyPrintRef() {
    exists (int l, int c | hasLocationInfo(_, l, c, _, _) |
      result = "def@" + l + ":" + c
    )
  }

  override string prettyPrintDef() { result = getDef().toString() }

  override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                     int endline, int endcolumn) {
    getDef().getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

/**
 * An SSA definition that does not correspond to an explicit variable definition.
 */
abstract class SSAImplicitDefinition extends SSADefinition {
  /**
   * INTERNAL: Do not use.
   *
   * Gets the definition kind to include in `prettyPrintRef`.
   */
  abstract string getKind();

  /** Gets the basic block to which this definition belongs. */
  abstract ReachableBasicBlock getBasicBlock();

  /** Gets the variable assigned by this definition. */
  override abstract TrackableVariable getVariable();

  override predicate assignsAt(ReachableBasicBlock bb, int i, TrackableVariable v) {
    bb = getBasicBlock() and v = getVariable() and i = -1
  }

  override string prettyPrintRef() {
    exists (int l, int c | hasLocationInfo(_, l, c, _, _) |
      result = getKind() + "@" + l + ":" + c
    )
  }

  override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                     int endline, int endcolumn) {
    endline = startline and endcolumn = startcolumn and
    getBasicBlock().getLocation().hasLocationInfo(filepath, startline, startcolumn, _, _)
  }
}

/**
 * An SSA definition representing the implicit initialization of a variable
 * at the beginning of its scope.
 */
class SSAImplicitInit extends SSAImplicitDefinition, TImplicitInit {
  override ReachableBasicBlock getBasicBlock() { this = TImplicitInit(result, _) }

  override TrackableVariable getVariable() { this = TImplicitInit(_, result) }

  override string getKind() { result = "implicitInit" }

  override string prettyPrintDef() {
    result = "implicit initialization of " + getVariable()
  }
}

/**
 * An SSA definition representing the capturing of a (trackable) variable
 * in the closure of a nested function.
 *
 * Capturing definitions appear at the beginning of such functions, as well as
 * after any `yield` expressions.
 */
class SSACapture extends SSAImplicitDefinition, TCapture {
  override ReachableBasicBlock getBasicBlock() { this = TCapture(result, _) }

  override TrackableVariable getVariable() { this = TCapture(_, result) }

  override string getKind() { result = "capture" }

  override string prettyPrintDef() {
    result = "capture variable " + getVariable()
  }
}

/**
 * An SSA definition that has no actual semantics, but simply serves to
 * merge or filter data flow.
 *
 * Phi nodes are the canonical example.
 */
abstract class SSAPseudoDefinition extends SSAImplicitDefinition {
  /**
   * Gets an input of this pseudo-definition.
   */
  SSADefinition getAnInput() {
    result = getAPseudoDefinitionInput(this)
  }

  /**
   * Gets the `i`th input of this pseudo-definition
   * (in lexicographical order, 1-based).
   */
  private SSADefinition getInput(int i) {
    result.prettyPrintRef() = rank[i](SSADefinition input |
      input = getAnInput() | input.prettyPrintRef()
    )
  }

  /**
   * Gets a textual representation of the inputs of this pseudo-definition
   * in lexicographical order, starting with the `i`th input.
   */
  private string ppInputs(int i) {
    result = ", " + getInput(i).prettyPrintRef() + ppInputs(i+1) or
    i = count(getAnInput())+1 and result = ""
  }

  /**
   * Gets a textual representation of the inputs of this pseudo-definition
   * in lexicographical order.
   */
  string ppInputs() {
    result = ppInputs(1).suffix(2)
  }
}

/** Holds if `nd` is a pseudo-definition and the result is one of its inputs. */
private SSADefinition getAPseudoDefinitionInput(SSADefinition nd) {
  exists (SSAPseudoDefinition psi | psi = nd |
    result = getDefReachingEndOf(psi.getVariable(),
                                 psi.getBasicBlock().getAPredecessor())
  )
}

/**
 * An SSA phi node, that is, a pseudo-definition for a variable at a point
 * in the flow graph where otherwise two or more definitions for the variable
 * would be visible.
 */
class SSAPhiNode extends SSAPseudoDefinition, TPhi {
  override ReachableBasicBlock getBasicBlock() { this = TPhi(result, _) }

  override TrackableVariable getVariable() { this = TPhi(_, result) }

  override string getKind() { result = "phi" }

  override string prettyPrintDef() {
    result = getVariable() + " = phi(" + ppInputs() + ")"
  }

  override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                     int endline, int endcolumn) {
    endline = startline and endcolumn = startcolumn and
    getBasicBlock().getLocation().hasLocationInfo(filepath, startline, startcolumn, _, _)
  }
}

/**
 * A refinement node, that is, a pseudo-definition for a variable at a point
 * in the flow graph where additional information about this variable becomes
 * available that may restrict its possible set of values.
 */
class SSARefinement extends SSAPseudoDefinition, TRefinement {
  /**
   * Gets the guard that induces this refinement.
   */
  GuardControlFlowNode getGuard() { this = TRefinement(_, result, _) }

  /**
   * Gets the refinement associated with this definition.
   */
  Refinement getRefinement() { result = getGuard().getTest() }

  override ReachableBasicBlock getBasicBlock() { this = TRefinement(result, _, _) }

  override TrackableVariable getVariable() { this = TRefinement(_, _, result) }

  override string getKind() { result = "refine" }

  override string prettyPrintDef() {
    result = getVariable() + " = refine[" + getGuard() + "](" + ppInputs() + ")"
  }

  override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                     int endline, int endcolumn) {
    getGuard().getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

/**
 * Gets the (1-based) rank of the `i`th node of `bb` among all SSA definitions
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
int defUseRank(TrackableVariable v, BasicBlock bb, int i) {
  i = rank[result](int j |
    any(SSADefinition ssa).assignsAt(bb, j, v) or
    bb.useAt(j, v, _)
  )
}

/**
 * Gets the number of SSA definitions and uses of `v` in `bb`.
 */
private
int lastDefUseRank(TrackableVariable v, BasicBlock bb) {
  result = max(defUseRank(v, bb, _))
}

/**
 * Gets the (1-based) rank of `def` among all SSA definitions and uses of `v` in `bb`.
 */
private
int ssaDefRank(TrackableVariable v, SSADefinition def, BasicBlock bb) {
  exists (int i | def.assignsAt(bb, i, v) | result = defUseRank(v, bb, i))
}

/**
 * Gets the unique SSA definition in `bb`, if it exists, whose value
 * reaches the `k`th definition or use of `v` in `bb`.
 */
private
SSADefinition getLocalDefAt(TrackableVariable v, ReachableBasicBlock bb, int k) {
  k = ssaDefRank(v, result, bb)
  or
  result = getLocalDefAt(v, bb, k-1) and k <= lastDefUseRank(v, bb) and
  not k = ssaDefRank(v, _, bb)
}

/**
 * Gets an SSA definition of `v` that reaches the end of basic block `bb`.
 */
private
SSADefinition getDefReachingEndOf(TrackableVariable v, BasicBlock bb) {
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
 * Gets the (unique) SSA definition of `v` in the same block as `u`
 * whose value reaches `u`, if any.
 */
private
SSADefinition getLocalDef(TrackableVariable v, VarUse u) {
  exists (BasicBlock bb, int i |
    bb.useAt(i, v, u) and
    result = getLocalDefAt(v, bb, defUseRank(v, bb, i))
  )
}

/**
 * Gets the unique SSA definition of `v` whose value reaches the use `u`.
 */
private
SSADefinition getDefinition(TrackableVariable v, VarUse u) {
  result = getLocalDef(v, u)
  or
  exists (BasicBlock bb | bb.useAt(_, v, u) |
    not exists(getLocalDef(v, u)) and
    result = getDefReachingEndOf(v, bb.getImmediateDominator())
  )
}
