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

/** Provides predicates for computing Enhanced SSA form 
 * Computation of ESSA form is identical to plain SSA form,
 * but what counts as a use of definition differs.
 */


import python
import semmle.dataflow.SSA


cached module EssaDefinitions {

    /** Whether `n` is a live update that is a definition of the variable `v`. */
    cached predicate variableUpdate(SsaSourceVariable v, ControlFlowNode n, BasicBlock b, int rankix, int i) {
        SsaCompute::variableDef(v, n, b, i) and
        SsaCompute::defUseRank(v, b, rankix, i) and
        (
            SsaCompute::defUseRank(v, b, rankix+1, _) and not SsaCompute::defRank(v, b, rankix+1, _)
            or
            not SsaCompute::defUseRank(v, b, rankix+1, _) and Liveness::liveAtExit(v, b)
        )
    }

    /** Holds if `def` is a pi-node for `v` on the edge `pred` -> `succ` */
    cached predicate piNode(SsaSourceVariable v, BasicBlock pred, BasicBlock succ) {
        v.hasRefinementEdge(_, pred, succ) and
        Liveness::liveAtEntry(v, succ)
    }

    /** A phi node for `v` at the beginning of basic block `b`. */
    cached predicate phiNode(SsaSourceVariable v, BasicBlock b) {
        (
            exists(BasicBlock def | def.dominanceFrontier(b) |
                SsaCompute::ssaDef(v, def)
            )
            or
            piNode(v, _, b) and strictcount(b.getAPredecessor()) > 1
        ) and
        Liveness::liveAtEntry(v, b)
    }

}

/* A note on numbering
 * In order to create an SSA graph, we need an order of definitions and uses within a basic block.
 * To do this we index definitions and uses as follows:
 *  Phi-functions have an index of -1, so precede all normal uses and definitions in a block.
 *  Pi-functions (on edges) have an index of -2 in the successor block, so precede all other uses and definitions, including phi-functions
 *  A use of a variable at at a CFG node is assumed to occur before any definition at the same node, so:
 *   * a use at the `j`th node of a block is given the index `2*j` and
 *   * a definition  at the `j`th node of a block is given the index `2*j + 1`.
 */

pragma [inline]
int phiIndex() { result = -1 }

pragma [inline]
int piIndex() { result = -2 }


private cached module SsaCompute {

    cached predicate variableDef(SsaSourceVariable v, ControlFlowNode n, BasicBlock b, int i) {
        (v.hasDefiningNode(n) or v.hasRefinement(_, n))
        and
        exists(int j |
            n = b.getNode(j) and 
            i = j*2 + 1
        )
    }

    /**
     * A ranking of the indices `i` at which there is an SSA definition or use of
     * `v` in the basic block `b`.
     *
     * Basic block indices are translated to rank indices in order to skip
     * irrelevant indices at which there is no definition or use when traversing
     * basic blocks.
     */
    cached predicate defUseRank(SsaSourceVariable v, BasicBlock b, int rankix, int i) {
      i = rank[rankix](int j | variableDef(v, _, b, j) or variableUse(v, _, b, j))
    }

    /** A definition of a variable occurring at the specified rank index in basic block `b`. */
    cached predicate defRank(SsaSourceVariable v, BasicBlock b, int rankix, int i) {
      variableDef(v, _, b, i) and
      defUseRank(v, b, rankix, i)
    }

    /** A `VarAccess` `use` of `v` in `b` at index `i`. */
    cached predicate variableUse(SsaSourceVariable v, ControlFlowNode use, BasicBlock b, int i) {
        (v.getAUse() = use or v.hasRefinement(use, _)) and
        exists(int j |
            b.getNode(j) = use and 
            i = 2*j
        )
    }

    /**
     * A definition of an SSA variable occurring at the specified position.
     * This is either a phi node, a `VariableUpdate`, or a parameter.
     */
    cached predicate ssaDef(SsaSourceVariable v, BasicBlock b) {
        EssaDefinitions::phiNode(v, b)
        or
        EssaDefinitions::variableUpdate(v, _, b, _, _)
        or
        EssaDefinitions::piNode(v, _, b)
    }

    /*
     * The construction of SSA form ensures that each use of a variable is
     * dominated by its definition. A definition of an SSA variable therefore
     * reaches a `ControlFlowNode` if it is the _closest_ SSA variable definition
     * that dominates the node. If two definitions dominate a node then one must
     * dominate the other, so therefore the definition of _closest_ is given by the
     * dominator tree. Thus, reaching definitions can be calculated in terms of
     * dominance.
     */

    /** The maximum rank index for the given variable and basic block. */
    cached int lastRank(SsaSourceVariable v, BasicBlock b) {
        result = max(int rankix | defUseRank(v, b, rankix, _))
        or
        not defUseRank(v, b, _, _) and (EssaDefinitions::phiNode(v, b) or EssaDefinitions::piNode(v, _, b)) and result = 0
    }

    private predicate ssaDefRank(SsaSourceVariable v, BasicBlock b, int rankix, int i) {
        EssaDefinitions::variableUpdate(v, _, b, rankix, i)
        or
        EssaDefinitions::phiNode(v, b) and rankix = 0 and i = phiIndex()
        or
        EssaDefinitions::piNode(v, _, b) and EssaDefinitions::phiNode(v, b) and rankix = -1 and i = piIndex()
        or
        EssaDefinitions::piNode(v, _, b) and not EssaDefinitions::phiNode(v, b) and rankix = 0 and i = piIndex()
    }

    /** The SSA definition reaches the rank index `rankix` in its own basic block `b`. */
    cached predicate ssaDefReachesRank(SsaSourceVariable v, BasicBlock b, int i, int rankix) {
      ssaDefRank(v, b, rankix, i) or
      ssaDefReachesRank(v, b, i, rankix-1) and rankix <= lastRank(v, b) and not ssaDefRank(v, b, rankix, _)
    }

    /**
     * The SSA definition of `v` at `def` reaches `use` in the same basic block
     * without crossing another SSA definition of `v`.
     */
    cached predicate ssaDefReachesUseWithinBlock(SsaSourceVariable v, BasicBlock b, int i, ControlFlowNode use) {
        exists(int rankix, int useix |
            ssaDefReachesRank(v, b, i, rankix) and
            defUseRank(v, b, rankix, useix) and
            variableUse(v, use, b, useix)
        )
    }

}

/*
 * Liveness analysis to restrict the size of the SSA representation.
 */
cached module Liveness {

    cached predicate liveAtExit(SsaSourceVariable v, BasicBlock b) {
        liveAtEntry(v, b.getASuccessor())
    }

    cached predicate liveAtEntry(SsaSourceVariable v, BasicBlock b) {
        SsaCompute::defUseRank(v, b, 1, _) and not SsaCompute::defRank(v, b, 1, _)
        or
        not SsaCompute::defUseRank(v, b, _, _) and liveAtExit(v, b)
    }

}

cached module SsaDefinitions {

    /**
     * The SSA definition of `v` at `def` reaches the end of a basic block `b`, at
     * which point it is still live, without crossing another SSA definition of `v`.
     */
    cached
    predicate reachesEndOfBlock(SsaSourceVariable v, BasicBlock defbb, int defindex, BasicBlock b) {
      Liveness::liveAtExit(v, b) and
      (
        defbb = b and SsaCompute::ssaDefReachesRank(v, defbb, defindex, SsaCompute::lastRank(v, b)) 
        or
        exists(BasicBlock idom |
          idom = b.getImmediateDominator() and 
          // It is sufficient to traverse the dominator graph, cf. discussion above.
          reachesEndOfBlock(v, defbb, defindex, idom) and
          not SsaCompute::ssaDef(v, b)
        )
      )
    }

    /**
     * The SSA definition of `v` at `(defbb, defindex)` reaches `use` without crossing another
     * SSA definition of `v`.
     */
    cached
    predicate reachesUse(SsaSourceVariable v, BasicBlock defbb, int defindex, ControlFlowNode use) {
      SsaCompute::ssaDefReachesUseWithinBlock(v, defbb, defindex, use) or
      exists(BasicBlock b |
        SsaCompute::variableUse(v, use, b, _) and
        reachesEndOfBlock(v, defbb, defindex, b.getAPredecessor()) and
        not SsaCompute::ssaDefReachesUseWithinBlock(v, b, _, use)
      )
    }
        /***
     * Holds if `(defbb, defindex)` is an SSA definition of `v` that reaches an exit without crossing another
     * SSA definition of `v`.
     */
    cached
    predicate reachesExit(SsaSourceVariable v, BasicBlock defbb, int defindex) {
        exists(BasicBlock last, ControlFlowNode use, int index |
            not Liveness::liveAtExit(v, last) and
            reachesUse(v, defbb, defindex, use) and
            SsaCompute::defUseRank(v, last, SsaCompute::lastRank(v, last), index) and
            SsaCompute::variableUse(v, use, last, index)
        )
    }

}
