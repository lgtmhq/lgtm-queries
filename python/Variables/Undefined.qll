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

import python
import Loop
import semmle.python.security.TaintTracking

/** Marker for "uninitialized". */
class Uninitialized extends TaintKind {

    Uninitialized() { this = "undefined" }

}

/** A source of an uninitialized variable.
 * Either the start of the scope or a deletion. 
 */
class UninitializedSource extends TaintedDefinition {

    UninitializedSource() {
        exists(FastLocalVariable var |
            this.getSourceVariable() = var and
            not var.escapes() |
            this instanceof ScopeEntryDefinition
            or
            this instanceof DeletionDefinition
        )
    }

    override predicate isSourceOf(TaintKind kind) {
        kind instanceof Uninitialized
    }

}

/** A loop where we are guaranteed (or is at least likely) to execute the body at least once. 
 */
class AtLeastOnceLoop extends DataFlowExtension::DataFlowVariable {

    AtLeastOnceLoop() {
        loop_entry_variables(this, _)
    }

    /* If we are guaranteed to iterate over a loop at least once, then we can prune any edges that
     * don't pass through the body.
     */
    override predicate prunedSuccessor(EssaVariable succ) {
        loop_entry_variables(this, succ)
    }

}

private predicate loop_entry_variables(EssaVariable pred, EssaVariable succ) {
    exists(PhiFunction phi, BasicBlock pb |
        loop_entry_edge(pb, phi.getBasicBlock()) and
        succ = phi.getVariable() and
        pred = phi.getInput(pb)
    )
}

private predicate loop_entry_edge(BasicBlock pred, BasicBlock loop) {
    pred = loop.getAPredecessor() and
    pred = loop.getImmediateDominator() and
    exists(Stmt s |
        loop_probably_executes_at_least_once(s) and
        s.getAFlowNode().getBasicBlock() = loop
    )
}

class UnitializedSanitizer extends Sanitizer {

    UnitializedSanitizer() { this = "use of variable" }

    predicate sanitizingDefinition(TaintKind taint, EssaDefinition def) {
        // An assignment cannot leave a variable uninitialized
        taint instanceof Uninitialized and
        (
            def instanceof AssignmentDefinition
            or
            def instanceof ExceptionCapture
            or
            def instanceof ParameterDefinition
        )
    }

    predicate postSanitizedVariable(TaintKind taint, EssaVariable var) {
        /* A use is a "sanitizer" of "uninitialized", as any use of an undefined
         * variable will raise, making the subsequent code unreacahable.
         */
        taint instanceof Uninitialized and
        exists(var.getASourceUse())
    }

}

/* Holds if `call` is a call of the form obj.method_name(...) and 
 * there is a function called `method_name` that can exit the program.
 */
private predicate maybe_call_to_exiting_function(CallNode call) {
    exists(FunctionObject exits, string name |
        call.getFunction().(AttrNode).getName() = name and
        exits.neverReturns() and exits.isNormalMethod() and
        exits.getName() = name
    )
}

/** Prune edges where the predecessor block looks like it might contain a call to an exit function. */
class ExitFunctionGuardedEdge extends DataFlowExtension::DataFlowVariable {

    predicate prunedSuccessor(EssaVariable succ) {
        exists(CallNode exit_call |
            succ.(PhiFunction).getInput(exit_call.getBasicBlock()) = this and
            maybe_call_to_exiting_function(exit_call)
        )
    }

}

