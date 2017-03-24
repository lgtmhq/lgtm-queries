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

/** SSA library */

import python

/** A single static assignment variable.
 * An SSA variable is a variable which is only assigned once (statically).
 * SSA variables can be defined as normal variables or by a phi node which can occur at joins in the flow graph.
 * Definitions without uses do not have a SSA variable.
 */
class SsaVariable extends @py_ssa_var{

    SsaVariable() {
        py_ssa_var(this, _)
    }

    /** Gets the source variable */
    Variable getVariable() {
        py_ssa_var(this, result)
    }

    /** Gets a use of this variable */
    ControlFlowNode getAUse() {
        py_ssa_use(result, this)
    }

    /** Gets the definition (which may be a deletion) of this SSA variable */
    ControlFlowNode getDefinition() {
        py_ssa_defn(this, result)
    }

    /** Gets an argument of the phi function defining this variable.
     * This predicate uses the raw SSA form produced by the extractor.
     * In general, you should use `getAPrunedPhiInput()` instead. */
    SsaVariable getAPhiInput() {
        py_ssa_phi(this, result)
    }

    /** Gets the edge(s) (result->this.getDefinition()) on which the SSA variable 'input' defines this SSA variable.
     * For each incoming edge `X->B`, where `B` is the the basic block containing this phi-node, only one of the input SSA variables
     * for this phi-node is live. This predicate returns the predecessor block such that the variable 'input'
     * is the live variable on the edge result->B.
     */
    BasicBlock getPredecessorBlockForPhiArgument(SsaVariable input) {
        input = this.getAPhiInput() and
        result = this.getAPredecessorBlockForPhi() and
        input.getDefinition().getBasicBlock().dominates(result) and
        /* Beware the case where an SSA variable that is an input on one edge dominates another edge.
         * Consider (in SSA form):
         * x0 = 0
         * if cond:
         *      x1 = 1
         * x2 = phi(x0, x1)
         * use(x2)
         * 
         * The definition of x0 dominates the exit from the block x1=1, even though it does not reach it.
         * Hence we need to check that no other definition dominates the edge and actually reaches it.
         * Note that if a dominates c and b dominates c, then either a dominates b or vice-versa.
         */
        not exists(SsaVariable other, BasicBlock other_def |
            not other = input and
            other = this.getAPhiInput() and
            other_def = other.getDefinition().getBasicBlock()
            |
            other_def.dominates(result) and
            input.getDefinition().getBasicBlock().strictlyDominates(other_def)
        )
    }

    /** Gets an argument of the phi function defining this variable, pruned of unlikely edges. */
    SsaVariable getAPrunedPhiInput() {
        result = this.getAPhiInput() and
        exists(BasicBlock incoming | incoming = this.getPredecessorBlockForPhiArgument(result) |
            not incoming.getLastNode().(RaisingNode).unlikelySuccessor(this.getDefinition())
        )
    }

    /** Gets a variable that ultimately defines this variable and is not itself defined by another variable */
    SsaVariable getAnUltimateDefinition() {
        result = this and not exists(this.getAPhiInput())
        or
        result = this.getAPhiInput().getAnUltimateDefinition()
    }

    string toString() {
        result = "SSA Variable " + this.getId()
    }

    Location getLocation() {
        result = this.getDefinition().getLocation()
    }

    /** Gets the id (name) of this variable */
    string getId() {
        result  = this.getVariable().getId()
    }

    /** Gets the incoming edges for a Phi node. */
    private BasicBlock getAPredecessorBlockForPhi() {
        exists(getAPhiInput()) and 
        result.getASuccessor() = this.getDefinition().getBasicBlock()
    }

    /** Gets the incoming edges for a Phi node, pruned of unlikely edges. */
    private BasicBlock getAPrunedPredecessorBlockForPhi() {
        result = this.getAPredecessorBlockForPhi() and
        not result.unlikelySuccessor(this.getDefinition().getBasicBlock())
    }

    /** Whether it is possible to reach a use of this variable without passing a definition */
    predicate reachableWithoutDefinition() {
        not exists(this.getDefinition()) and not py_ssa_phi(this, _)
        or
        exists(SsaVariable var | var = this.getAPhiInput() | var.reachableWithoutDefinition())
        or
        /* For phi-nodes, there must be a corresponding phi-input for each control-flow
         * predecessor. Otherwise, the variable will be undefined on that incoming edge.
         * WARNING: the same phi-input may cover multiple predecessors, so this check
         *          cannot be done by counting.
         */
        exists(BasicBlock incoming |
            incoming = this.getAPredecessorBlockForPhi() and
            not this.getAPhiInput().getDefinition().getBasicBlock().dominates(incoming)
        )
    }

    /** Whether this variable may be undefined */
    predicate maybeUndefined() {
        not exists(this.getDefinition()) and not py_ssa_phi(this, _) and not this.implicitlyDefined()
        or
        this.getDefinition().isDelete()
        or
        exists(SsaVariable var | var = this.getAPrunedPhiInput() | var.maybeUndefined())
        or
        /* For phi-nodes, there must be a corresponding phi-input for each control-flow
         * predecessor. Otherwise, the variable will be undefined on that incoming edge.
         * WARNING: the same phi-input may cover multiple predecessors, so this check
         *          cannot be done by counting.
         */
        exists(BasicBlock incoming |
            reaches_end(incoming) and
            incoming = this.getAPrunedPredecessorBlockForPhi() and
            not this.getAPhiInput().getDefinition().getBasicBlock().dominates(incoming)
        )
    }

    private predicate implicitlyDefined() {
        not exists(this.getDefinition()) and not py_ssa_phi(this, _) and
        exists(GlobalVariable var | this.getVariable() = var |
               globallyDefinedName(var.getId()) or
               var.getId() = "__path__" and ((Module)var.getScope()).isPackageInit()
        )
    }

    /** Gets the global variable that is accessed if this local is undefined. 
     *  Only applies to local variables in class scopes.
     */
    GlobalVariable getFallbackGlobal() {
        exists(LocalVariable local, Class cls | this.getVariable() = local |
            local.getScope() = cls and
            result.getScope() = cls.getScope() and
            result.getId() = local.getId() and
            not exists(this.getDefinition())
        )
    }

    /* Whether this SSA variable is the first parameter of a method 
     * (regardless of whether it is actually called self or not)
     */
    predicate isSelf() {
        exists(Function func | 
            func.isMethod()
            and
            this.getDefinition().getNode() = func.getArg(0)
        )
    }
}

private predicate reaches_end(BasicBlock b) {
    not exits_early(b)
    and
    (
      /* Entry point */
      not exists(BasicBlock prev | prev.getASuccessor() = b) 
      or
      exists(BasicBlock prev | prev.getASuccessor() = b |
          reaches_end(prev)
      )
    )
}

private predicate exits_early(BasicBlock b) {
    exists(FunctionObject f |
        f.neverReturns() and
        f.getACall().getBasicBlock() = b
    )
}

private predicate gettext_installed() {
    // Good enough (and fast) approximation
    exists(Module m | m.getName() = "gettext")
}

private predicate builtin_constant(string name) {
    exists(builtin_object(name))
    or
    name = "WindowsError"
    or
    name = "_" and gettext_installed()
}

private predicate auto_name(string name) {
  name = "__file__" or name = "__builtins__" or name = "__name__"
}

/** Whether this name is (almost) always defined, ie. it is a builtin or VM defined name */
predicate globallyDefinedName(string name) {
   builtin_constant(name) or auto_name(name)
}

private newtype TGlobalSsaVariable = 
    TGlobalSsaVariableDefn(GlobalVariable v, ControlFlowNode node) {
        final_global_ssa_defn(v, node, _)
    }

/** A global single static assignment variable.
 * A GSSA variable is a global variable which is only assigned once (statically).
 * GSSA variables are like SSA variables, but for global variables.
 * Like SSA variables they can by defined like normal variables or by phi nodes.
 * In addition they can be defined in several other ways:
 * 
 * 1. At a call-site, when the callee redefines the global variable
 * 2. At scope entry when a temporally-preceding scope has defined the global variable.
 * 3. At function entry, inheriting the GSSA value from a caller
 * 4. At class entry, inheriting the GSSA value from the enclosing scope.
 */

class GlobalSsaVariable extends TGlobalSsaVariable {

    GlobalVariable getVariable() {
        this = TGlobalSsaVariableDefn(result, _)
    }

    string getId() {
        result = this.getVariable().getId()
    }

    ControlFlowNode getDefinition() {
        this = TGlobalSsaVariableDefn(_, result)
    }

    string toString() {
        result = "GSSA Variable " + this.getId()
    }

    NameNode getAUse() {
        this.getDefinition() = final_get_global_ssa_defn(this.getVariable(), result)
    }


    /** Whether this variable may be undefined. */
    predicate maybeUndefined() {
        this.getDefinition().isDelete()
    }

}

class PhiGlobalSsaVariable extends GlobalSsaVariable {

    PhiGlobalSsaVariable() {
        final_global_phi_definition(this.getVariable(), this.getDefinition())
    }

    /** Gets the edge(s) `result->this.getDefinition()` on which the GSSA variable 'input' defines this GSSA variable.
     * For each incoming edge `X->B`, where `B` is the the basic block containing this phi-node, only one of the input GSSA variables
     * for this phi-node is live. This predicate returns the predecessor block such that the variable 'input'
     * is the live variable on the edge `result->B`.
     *
     * This may include inputs that are inferred by type-inference to be highly unlikely or impossible.
     * In general, you should use `getPrunedPredecessorBlockForArgument(input)` instead.
     */
    BasicBlock getPredecessorBlockForArgument(GlobalSsaVariable input) {
        input = TGlobalSsaVariableDefn(this.getVariable(),
            final_get_phi_argument_for_predecessor_block(this.getVariable(), this.getDefinition(), result)
        )
    }

    /** As `getPredecessorBlockForPhiArgument(input)`, but pruned of unlikely edges. */
    BasicBlock getPrunedPredecessorBlockForArgument(GlobalSsaVariable input) {
        result = getPredecessorBlockForArgument(input) and
        not result.unlikelySuccessor(input.getDefinition())
    }

    /** Gets an argument of the phi function defining this variable.
     * This may include inputs that are inferred by type-inference to be highly unlikely or impossible.
     * In general, you should use `getAPrunedInput()` instead. */
    GlobalSsaVariable getAPhiInput() {
        exists(this.getPredecessorBlockForArgument(result))
    }

    /** Gets an argument of the phi function defining this variable, pruned of unlikely edges. */
    GlobalSsaVariable getAPrunedInput() {
        exists(this.getPrunedPredecessorBlockForArgument(result))
    }

    /** Whether this variable may be undefined. */
    predicate maybeUndefined() {
        exists(GlobalSsaVariable var | var = this.getAPrunedInput() | var.maybeUndefined())
        or
        /* For phi-nodes, there must be a corresponding phi-input for each control-flow
         * predecessor. Otherwise, the variable will be undefined on that incoming edge.
         * For example,
         * if cond:
         *    x0 = "eggs"
         * x1 = phi(x0) # x1 is may be undefined as there is no phi input if `cond` is false.
         */
        exists(BasicBlock incoming |
            reaches_end(incoming) and
            incoming.getASuccessor() = this.getDefinition() and
            not exists(GlobalSsaVariable input |
                incoming = this.getPrunedPredecessorBlockForArgument(input)
            )
        )
    }

}
