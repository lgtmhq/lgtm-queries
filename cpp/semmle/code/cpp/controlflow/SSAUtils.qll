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

import cpp
import semmle.code.cpp.controlflow.Dominance
import semmle.code.cpp.controlflow.SSA // must be imported for proper caching of SSAHelper
import semmle.code.cpp.rangeanalysis.RangeSSA // must be imported for proper caching of SSAHelper

/* The dominance frontier of a block `x` is the set of all blocks `w` such that
 * `x` dominates a predecessor of `w` but does not strictly dominate `w`. */
pragma[noinline]
private predicate dominanceFrontier(BasicBlock x, BasicBlock w) {
    bbDominates(x, w.getAPredecessor()) and not bbStrictlyDominates(x, w)
}

/**
 * Extended version of `definition` that also includes parameters but excludes
 * static variables.
 */
predicate var_definition(LocalScopeVariable v, ControlFlowNode node) {
    not v.isStatic()
    and
    not addressTakenVariable(v)
    and
    not unreachable(node)
    and
    (if isReferenceVar(v)
       then // Assignments to reference variables modify the referenced
            // value, not the reference itself. So reference variables only
            // have two kinds of definition: initializers and parameters.
            node = v.getInitializer().getExpr()
       else definition(v, node))
    or
    v instanceof Parameter and exists(BasicBlock b | b.getStart() = node and not exists(b.getAPredecessor()) and
                                      b = v.(Parameter).getFunction().getEntryPoint())
}

/**
 * Holds if `e` is used in a context where it is never dereferenced.  This
 * is a helper predicate for `addressTakenVariable`. It was added because
 * of this macro, which is used in the Linux source code:
 *
 *   #define min(x, y) ({        \
 *       typeof(x) _min1 = (x);      \
 *       typeof(y) _min2 = (y);      \
 *       (void) (&_min1 == &_min2);    \
 *       _min1 < _min2 ? _min1 : _min2; })
 *
 * The addresses of `_min1` and `_min2` are taken, but it does not cause
 * any aliasing, so there is no need to disable SSA for these variables.
 */
private predicate neverDereferenced(Expr e) {
  e.getParent() instanceof ComparisonOperation or
  e.getParent() instanceof ExprStmt or
  neverDereferenced(e.getParent().(PointerAddExpr)) or
  neverDereferenced(e.getParent().(PointerSubExpr))
}

/**
 * Stack variables that have their address taken are excluded from the
 * analysis because the pointer could be used to change the value at
 * any moment.
 */
private predicate addressTakenVariable(LocalScopeVariable var) {
    // If the type of the variable is a reference type, then it is safe (as
    // far as SSA is concerned) to take its address, because this does not
    // enable the variable to be modified indirectly. Obviously the
    // referenced value can change, but that is not the same thing as
    // changing which value the reference points to. SSA tracks the latter,
    // but the target of a reference is immutable so reference variables
    // always have exactly one definition.
    not isReferenceVar(var)
    and

    // Find a VariableAccess that takes the address of `var`.
    exists (VariableAccess va
    | va = var.getAnAccess() and

      // If the address is passed to a function then we will trust that it
      // is only used to modify the variable for the duration of the
      // function call.
      not exists(Call call | call.passesByReference(_, va))

    | // Taking the address.
      exists (AddressOfExpr addrExpr
      | addrExpr.getOperand() = va
        and

        // If the address is never dereferenced then there is no concern
        // about aliasing, so we can safely ignore it.
        not neverDereferenced(addrExpr)
        and

        // If the pointer is const then we will trust that it will not be
        // used to modify the variable.
        not (addrExpr.getFullyConverted().getUnderlyingType().(PointerType)
                     .getBaseType().isConst()))
      or

      // Converting a variable to a reference is the same thing as taking
      // its address.
      exists (ReferenceType rt
      | rt = va.getFullyConverted().getUnderlyingType() and

        // If the reference is const then we will trust that it will not be
        // used to modify the variable.
        not rt.getBaseType().isConst()))
}

private predicate isReferenceVar(LocalScopeVariable v) {
  v.getType().getUnspecifiedType() instanceof ReferenceType
}

/**
 * This predicate is the same as `var_definition`, but annotated with
 * the basic block and index of the control flow node.
 */
private predicate variableUpdate(LocalScopeVariable v, ControlFlowNode n, BasicBlock b, int i) {
  var_definition(v, n) and n = b.getNode(i)
}

private predicate ssa_use(LocalScopeVariable v, VariableAccess node, BasicBlock b, int index) {
    useOfVar(v, node) and b.getNode(index) = node
}

cached private predicate live_at_start_of_bb(LocalScopeVariable v, BasicBlock b) {
    exists (int i | ssa_use(v, _, b, i) |
      not exists (int j | variableUpdate(v, _, b, j) | j < i))
    or
    (live_at_exit_of_bb(v, b) and not variableUpdate(v, _, b, _))
}

pragma[noinline]
private predicate live_at_exit_of_bb(LocalScopeVariable v, BasicBlock b) {
    live_at_start_of_bb(v, b.getASuccessor())
}

/** Common SSA logic for standard SSA and range-analysis SSA. */
library class SSAHelper extends int {
    /* 0 = StandardSSA, 1 = RangeSSA */
    SSAHelper() { this in [0 .. 1] }

    /**
     * Override to insert a custom phi node for variable `v` at the start of
     * basic block `b`.
     */
    predicate custom_phi_node(LocalScopeVariable v, BasicBlock b) { none() }

    /**
     * Remove any custom phi nodes that are invalid.
     */
    private predicate sanitized_custom_phi_node(LocalScopeVariable v, BasicBlock b) {
      custom_phi_node(v,b) and
      not addressTakenVariable(v) and
      not isReferenceVar(v) and
      b.isReachable()
    }

    /**
     * Holds if there is a phi node for variable `v` at the start of basic block
     * `b`.
     */
    cached predicate phi_node(LocalScopeVariable v, BasicBlock b) {
        frontier_phi_node(v,b) or sanitized_custom_phi_node(v,b)
    }

    /**
     * A phi node is required for variable `v` at the start of basic block `b`
     * if there exists a basic block `x` such that `b` is in the dominance
     * frontier of `x` and `v` is defined in `x` (including phi-nodes as
     * definitions).  This is known as the iterated dominance frontier.  See
     * Modern Compiler Implementation by Andrew Appel.
     */
    private predicate frontier_phi_node(LocalScopeVariable v, BasicBlock b) {
        exists(BasicBlock x | dominanceFrontier(x, b) and ssa_defn(v, _, x, _))
        /* We can also eliminate those nodes where the variable is not live on any incoming edge */
        and live_at_start_of_bb(v, b)
    }

    /**
     * Holds if `v` is defined, for the purpose of SSA, at `node`, which is at
     * position `index` in block `b`. This includes definitions from phi nodes.
     */
    predicate ssa_defn(LocalScopeVariable v, ControlFlowNode node, BasicBlock b, int index) {
        phi_node(v, b) and b.getStart() = node and index = 0
        or
        variableUpdate(v, node, b, index)
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

    /**
     * A ranking of the indices `i` at which there is an SSA definition or use of
     * `v` in the basic block `b`.
     *
     * Basic block indices are translated to rank indices in order to skip
     * irrelevant indices at which there is no definition or use when traversing
     * basic blocks.
     */
    private predicate defUseRank(LocalScopeVariable v, BasicBlock b, int rankix, int i) {
      i = rank[rankix](int j | ssa_defn(v, _, b, j) or ssa_use(v, _, b, j))
    }

    /** Gets the maximum rank index for the given variable and basic block. */
    private int lastRank(LocalScopeVariable v, BasicBlock b) {
      result = max(int rankix | defUseRank(v, b, rankix, _))
    }

    /**
     * Holds if SSA variable `(v, def)` is defined at rank index `rankix` in
     * basic block `b`.
     */
    private predicate ssaDefRank(LocalScopeVariable v, ControlFlowNode def, BasicBlock b, int rankix) {
        exists(int i
        | ssa_defn(v, def, b, i) and
          defUseRank(v, b, rankix, i))
    }

    /**
     * Holds if SSA variable `(v, def)` reaches the rank index `rankix` in its
     * own basic block `b`.
     */
    private predicate ssaDefReachesRank(LocalScopeVariable v, ControlFlowNode def, BasicBlock b, int rankix) {
        ssaDefRank(v, def, b, rankix)
        or
        (ssaDefReachesRank(v, def, b, rankix-1) and
         rankix <= lastRank(v, b) and  // Without this, the predicate would be infinite.
         not ssaDefRank(v, _, b, rankix))
    }

    /** Holds if SSA variable `(v, def)` reaches the end of block `b`. */
    predicate ssaDefinitionReachesEndOfBB(LocalScopeVariable v, ControlFlowNode def, BasicBlock b) {
      (live_at_exit_of_bb(v, b) and ssaDefReachesRank(v, def, b, lastRank(v, b)))
      or
      exists (BasicBlock idom |
        ssaDefinitionReachesEndOfBB(v, def, idom) and
        noDefinitionsSinceIDominator(v, idom, b)
      )
    }

    /**
     * Helper predicate for ssaDefinitionReachesEndOfBB. If there is no
     * definition of `v` in basic block `b`, then any definition of `v`
     * that reaches the end of `idom` (the immediate dominator of `b`) also
     * reaches the end of `b`.
     */
    pragma[noinline]
    private predicate noDefinitionsSinceIDominator(LocalScopeVariable v, BasicBlock idom, BasicBlock b) {
        bbIDominates(idom, b) and // It is sufficient to traverse the dominator graph, cf. discussion above.
        live_at_exit_of_bb(v, b) and
        not ssa_defn(v, _, b, _)
    }

    /**
     * Holds if SSA variable `(v, def)` reaches `use` within the same basic
     * block, where `use` is a `VariableAccess` of `v`.
     */
    private predicate ssaDefinitionReachesUseWithinBB(LocalScopeVariable v, ControlFlowNode def, Expr use) {
        exists (BasicBlock b, int rankix, int i
        | ssaDefReachesRank(v, def, b, rankix) and
          defUseRank(v, b, rankix, i) and
          ssa_use(v, use, b, i))
    }

    /**
     * Holds if SSA variable `(v, def)` reaches the control-flow node `use`.
     */
    private
    predicate ssaDefinitionReaches(LocalScopeVariable v, ControlFlowNode def, Expr use) {
        ssaDefinitionReachesUseWithinBB(v, def, use) or
        exists (BasicBlock b
        | ssa_use(v, use, b, _) and
          ssaDefinitionReachesEndOfBB(v, def, b.getAPredecessor()) and
          not ssaDefinitionReachesUseWithinBB(v, _, use))
    }

    /**
     * Gets a string representation of the SSA variable represented by the pair
     * `(node, v)`.
     */
    string toString(ControlFlowNode node, LocalScopeVariable v) {
        if phi_node(v, (BasicBlock)node) then
            result = "SSA phi(" + v.getName() + ")"
        else
            (ssa_defn(v, node, _, _) and result = "SSA def(" + v.getName() + ")")
    }

    /**
     * Holds if SSA variable `(v, def)` reaches `result`, where `result` is an
     * access of `v`.
     */
    cached VariableAccess getAUse(ControlFlowNode def, LocalScopeVariable v) {
        ssaDefinitionReaches(v, def, result)
        and
        ssa_use(v, result, _, _)
    }
}
