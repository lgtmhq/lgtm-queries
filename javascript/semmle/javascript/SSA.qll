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
 * any call graph information. Hence we can only deal with local variables
 * that are not assigned to outside the function that declares them (though
 * they may be read by nested functions).
 *
 * Such variables are called _SSA source variables_ or _SSA-convertible
 * variables_. They can be treated as purely local within their declaring
 * function, since any assignments to the variable must be within that
 * function.
 *
 * Within each nested function `f` that accesses a captured variable
 * `x`, we introduce a pseudo-assignment to `x` called a _capture_ of `x`
 * at the beginning of the function that (conceptually) captures
 * the current value of `x`.
 *
 * Additionally, if `f` is a generator containing a `yield` expression,
 * each `yield` is considered to "re-capture" the current value of `x`.
 * This is necessary because, in general, the `yield` might transfer control
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
 * Here, `x` is SSA-convertible (since it is only assigned within `k`),
 * so `iter` has a pseudo-assignment for `x` at its beginning.
 * Additionally, the `yield` is also counted as an assignment to `x`,
 * which reflects the fact that `x` is incremented between the
 * two `console.log` calls.
 */

import javascript
private import semmle.javascript.flow.Refinements

/**
 * A variable that can be SSA converted, meaning that all its definitions
 * appear in the container inside which it is declared.
 */
class SsaSourceVariable extends LocalVariable {
  SsaSourceVariable() {
    exists (StmtContainer sc | sc = getDeclaringContainer() |
      forall (LValue def | def = getAnAccess() |
        def.getContainer() = sc
      )
    )
  }
}

private module Internal {
  /**
   * A data type representing SSA definitions.
   *
   * We distinguish five kinds of SSA definitions:
   *
   *   1. Explicit definitions wrapping a `VarDef` node in the CFG.
   *   2. Implicit initializations of locals (including `arguments`) at
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
  newtype TSsaDefinition =
       TExplicitDef(ReachableBasicBlock bb, int i, VarDef d, SsaSourceVariable v) {
         bb.defAt(i, v, d) and not v instanceof PurelyLocalVariable or
         bb.localLiveDefAt(v, i, d)
       }
    or TImplicitInit(EntryBasicBlock bb, SsaSourceVariable v) {
         bb.getContainer() = v.getDeclaringContainer() and
         bb.localIsLiveAtEntry(v)
       }
    or TCapture(ReachableBasicBlock bb, int i, SsaSourceVariable v) {
         exists (BasicBlock liveBB |
           liveBB.localIsLiveAtEntry(v) and liveBB.getContainer() != v.getDeclaringContainer() |
           // local variable capture at the beginning of a nested function
           bb instanceof EntryBasicBlock and i = 0 and liveBB = bb
           or
           // local variable re-capture after a `yield` expression
           liveBB.getFirstNode().getAPredecessor() = (YieldExpr)bb.getNode(i)
         )
       }
    or TPhi(ReachableJoinBlock bb, SsaSourceVariable v) {
         bb.localIsLiveAtEntry(v) and
         exists (ReachableBasicBlock defbb, SsaDefinition def |
          def.definesAt(defbb, _, v) and
          bb.inDominanceFrontierOf(defbb)
         )
       }
    or TRefinement(ReachableBasicBlock bb, GuardControlFlowNode guard, SsaSourceVariable v) {
         bb.getNode(0) = guard and
         guard.getTest().(Refinement).getRefinedVar() = v and
         bb.localIsLiveAtEntry(v)
       }
}
private import Internal

/**
 * An SSA variable.
 */
class SsaVariable extends TSsaDefinition {
  /** Gets the source variable corresponding to this SSA variable. */
  SsaSourceVariable getSourceVariable() {
    result = this.(SsaDefinition).getSourceVariable()
  }

  /** Gets the (unique) definition of this SSA variable. */
  SsaDefinition getDefinition() {
    result = this
  }

  /** Gets a use that refers to this SSA variable. */
  VarUse getAUse() { this = getDefinition(getSourceVariable(), result) }

  /** Gets a textual representation of this element. */
  string toString() {
    result = getDefinition().prettyPrintRef()
  }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/docs/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                            int endline, int endcolumn) {
    getDefinition().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

/**
 * An SSA definition.
 */
class SsaDefinition extends TSsaDefinition {
  /** Gets the SSA variable defined by this definition. */
  SsaVariable getVariable() {
    result = this
  }

  /** Gets the source variable defined by this definition. */
  abstract SsaSourceVariable getSourceVariable();

  /**
   * Gets the basic block to which this definition belongs.
   *
   * Currently, all SSA definitions belong to a basic block, but the representation of
   * implicit definitions might change in the future, making this no longer true.
   */
  abstract ReachableBasicBlock getBasicBlock();

/**
   * INTERNAL: Use `getBasicBlock()` and `getSourceVariable()` instead.
   *
   * Holds if this is a definition of source variable `v` at index `idx` in basic block `bb`.
   *
   * Phi nodes are considered to be at index `-1`, all other definitions at the index of
   * the control flow node they correspond to.
   */
  abstract predicate definesAt(ReachableBasicBlock bb, int idx, SsaSourceVariable v);

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
}

/**
 * An SSA definition that corresponds to an explicit assignment or other variable definition.
 */
class SsaExplicitDefinition extends SsaDefinition, TExplicitDef {
  override predicate definesAt(ReachableBasicBlock bb, int i, SsaSourceVariable v) {
    this = TExplicitDef(bb, i, _, v)
  }

  /** This SSA definition corresponds to the definition of `v` at `def`. */
  predicate defines(VarDef d, SsaSourceVariable v) {
    this = TExplicitDef(_, _, d, v)
  }

  /** The variable definition wrapped by this SSA definition. */
  VarDef getDef() {
    this = TExplicitDef(_, _, result, _)
  }

  /** Gets the basic block to which this definition belongs. */
  override ReachableBasicBlock getBasicBlock() {
    definesAt(result, _, _)
  }

  override SsaSourceVariable getSourceVariable() {
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
abstract class SsaImplicitDefinition extends SsaDefinition {
  /**
   * INTERNAL: Do not use.
   *
   * Gets the definition kind to include in `prettyPrintRef`.
   */
  abstract string getKind();

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
class SsaImplicitInit extends SsaImplicitDefinition, TImplicitInit {
  override predicate definesAt(ReachableBasicBlock bb, int i, SsaSourceVariable v) {
    bb = getBasicBlock() and v = getSourceVariable() and i = 0
  }

  override ReachableBasicBlock getBasicBlock() { this = TImplicitInit(result, _) }

  override SsaSourceVariable getSourceVariable() { this = TImplicitInit(_, result) }

  override string getKind() { result = "implicitInit" }

  override string prettyPrintDef() {
    result = "implicit initialization of " + getSourceVariable()
  }
}

/**
 * An SSA definition representing the capturing of an SSA-convertible variable
 * in the closure of a nested function.
 *
 * Capturing definitions appear at the beginning of such functions, as well as
 * after any `yield` expressions.
 */
class SsaVariableCapture extends SsaImplicitDefinition, TCapture {
  override predicate definesAt(ReachableBasicBlock bb, int i, SsaSourceVariable v) {
    this = TCapture(bb, i, v)
  }

  override ReachableBasicBlock getBasicBlock() { this = TCapture(result, _, _) }

  override SsaSourceVariable getSourceVariable() { this = TCapture(_, _, result) }

  override string getKind() { result = "capture" }

  override string prettyPrintDef() {
    result = "capture variable " + getSourceVariable()
  }

  override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                     int endline, int endcolumn) {
    exists (ReachableBasicBlock bb, int i | this = TCapture(bb, i, _) |
      bb.getNode(i).getLocation().hasLocationInfo(filepath, startline, startcolumn,
                                                            endline, endcolumn)
    )
  }
}

/**
 * An SSA definition that has no actual semantics, but simply serves to
 * merge or filter data flow.
 *
 * Phi nodes are the canonical example.
 */
abstract class SsaPseudoDefinition extends SsaImplicitDefinition {
  /**
   * Gets an input of this pseudo-definition.
   */
  abstract SsaVariable getAnInput();

  /**
   * Gets a textual representation of the inputs of this pseudo-definition
   * in lexicographical order.
   */
  string ppInputs() {
    result = concat(getAnInput().getDefinition().prettyPrintRef(), ", ")
  }
}

/**
 * An SSA phi node, that is, a pseudo-definition for a variable at a point
 * in the flow graph where otherwise two or more definitions for the variable
 * would be visible.
 */
class SsaPhiNode extends SsaPseudoDefinition, TPhi {
  override SsaVariable getAnInput() {
    result = getDefReachingEndOf(getSourceVariable(), getBasicBlock().getAPredecessor())
  }

  override predicate definesAt(ReachableBasicBlock bb, int i, SsaSourceVariable v) {
    bb = getBasicBlock() and v = getSourceVariable() and i = -1
  }

  override ReachableBasicBlock getBasicBlock() { this = TPhi(result, _) }

  override SsaSourceVariable getSourceVariable() { this = TPhi(_, result) }

  override string getKind() { result = "phi" }

  override string prettyPrintDef() {
    result = getSourceVariable() + " = phi(" + ppInputs() + ")"
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
class SsaRefinementNode extends SsaPseudoDefinition, TRefinement {
  /**
   * Gets the guard that induces this refinement.
   */
  GuardControlFlowNode getGuard() { this = TRefinement(_, result, _) }

  /**
   * Gets the refinement associated with this definition.
   */
  Refinement getRefinement() { result = getGuard().getTest() }

  override SsaVariable getAnInput() {
    exists (SsaSourceVariable v, BasicBlock bb | v = getSourceVariable() and bb = getBasicBlock() |
      if exists(SsaPhiNode phi | phi.definesAt(bb, _, v)) then
        result.(SsaPhiNode).definesAt(bb, _, v)
      else
        result = getDefReachingEndOf(v, bb.getAPredecessor())
    )
  }

  override predicate definesAt(ReachableBasicBlock bb, int i, SsaSourceVariable v) {
    exists (ControlFlowNode nd | this = TRefinement(bb, nd, v) | nd = bb.getNode(i))
  }

  override ReachableBasicBlock getBasicBlock() { this = TRefinement(result, _, _) }

  override SsaSourceVariable getSourceVariable() { this = TRefinement(_, _, result) }

  override string getKind() { result = "refine[" + getGuard() + "]" }

  override string prettyPrintDef() {
    result = getSourceVariable() + " = refine[" + getGuard() + "](" + ppInputs() + ")"
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
int defUseRank(SsaSourceVariable v, BasicBlock bb, int i) {
  i = rank[result](int j |
    any(SsaDefinition ssa).definesAt(bb, j, v) or
    bb.useAt(j, v, _)
  )
}

/**
 * Gets the number of SSA definitions and uses of `v` in `bb`.
 */
private
int lastDefUseRank(SsaSourceVariable v, BasicBlock bb) {
  result = max(defUseRank(v, bb, _))
}

/**
 * Gets the (1-based) rank of `def` among all SSA definitions and uses of `v` in `bb`.
 */
private
int ssaDefRank(SsaSourceVariable v, SsaDefinition def, BasicBlock bb) {
  exists (int i | def.definesAt(bb, i, v) | result = defUseRank(v, bb, i))
}

/**
 * Gets the unique SSA definition in `bb`, if it exists, whose value
 * reaches the `k`th definition or use of `v` in `bb`.
 */
private
SsaDefinition getLocalDefAt(SsaSourceVariable v, ReachableBasicBlock bb, int k) {
  k = ssaDefRank(v, result, bb)
  or
  result = getLocalDefAt(v, bb, k-1) and k <= lastDefUseRank(v, bb) and
  not k = ssaDefRank(v, _, bb)
}

/**
 * Gets an SSA definition of `v` that reaches the end of basic block `bb`.
 */
private
SsaDefinition getDefReachingEndOf(SsaSourceVariable v, BasicBlock bb) {
  bb.getASuccessor().localIsLiveAtEntry(v) and
  (
    result = getLocalDefAt(v, bb, lastDefUseRank(v, bb))
    or
    /* In SSA form, the (unique) reaching definition of a use is the closest
     * definition that dominates the use. If two definitions dominate a node
     * then one must dominate the other, so we can find the reaching definition
     * by following the idominance relation backwards. */
    result = getDefReachingEndOf(v, bb.getImmediateDominator()) and
    not exists (SsaDefinition ssa | ssa.definesAt(bb, _, v))
  )
}

/**
 * Gets the (unique) SSA definition of `v` in the same block as `u`
 * whose value reaches `u`, if any.
 */
private
SsaDefinition getLocalDef(SsaSourceVariable v, VarUse u) {
  exists (BasicBlock bb, int i |
    bb.useAt(i, v, u) and
    result = getLocalDefAt(v, bb, defUseRank(v, bb, i))
  )
}

/**
 * Gets the unique SSA definition of `v` whose value reaches the use `u`.
 */
private
SsaDefinition getDefinition(SsaSourceVariable v, VarUse u) {
  result = getLocalDef(v, u)
  or
  exists (BasicBlock bb | bb.useAt(_, v, u) |
    not exists(getLocalDef(v, u)) and
    result = getDefReachingEndOf(v, bb.getImmediateDominator())
  )
}
