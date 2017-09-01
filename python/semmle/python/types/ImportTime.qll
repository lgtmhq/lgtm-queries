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

import python

/** An ImportTimeScope is any scope that is not nested within a function and will thus be executed if its
 * enclosing module is imported. 
 * Note however, that if a scope is not an ImportTimeScope it may still be executed at import time.
 * This is an artificial approximation, which is necessary for static analysis.
 */
class ImportTimeScope extends Scope {
 
    ImportTimeScope() {
        not this.getEnclosingScope*() instanceof Function
    }

    /** Whether this scope explicitly defines 'name'. 
     * Does not cover implicit definitions be import * */
    pragma[nomagic]
    predicate definesName(string name) {
        exists(SsaVariable var | name = var.getId() and var.getAUse() = this.getANormalExit())
    }

    /** Holds if the control flow passes from `outer` to `inner` when this scope starts executing */
    predicate entryEdge(ControlFlowNode outer, ControlFlowNode inner) {
        inner = this.getEntryNode() and
        outer.getNode().(ClassExpr).getInnerScope() = this
    }

    /** Gets the global variable that is used during lookup, should `var` be undefined. */
    GlobalVariable getOuterVariable(LocalVariable var) {
        this instanceof Class and
        var.getScope() = this and
        result.getScope() = this.getEnclosingModule() and
        var.getId() = result.getId()
    }

}
