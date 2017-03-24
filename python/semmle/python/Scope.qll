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

/** A Scope. A scope is the lexical extent over which all identifiers with the same name refer to the same variable.
    Modules, Classes and Functions are all Scopes. There are no other scopes.
    The scopes for expressions that create new scopes, lambdas and comprehensions, are handled by creating an anonymous Function. */
class Scope extends Scope_ {

    Module getEnclosingModule() {
        result = this.getEnclosingScope().getEnclosingModule()
    }

    /** This method will be deprecated in the next release. Please use `getEnclosingScope()` instead.
     * The reason for this is to avoid confusion around use of `x.getScope+()` where `x` might be an
     * `AstNode` or a `Variable`. Forcing the users to write `x.getScope().getEnclosingScope*()` ensures that
     * the apparent semantics and the actual semantics coincide.
     * [ Gets the scope enclosing this scope (modules have no enclosing scope) ]
     */
    Scope getScope() {
        none()
    }

    /** Gets the scope enclosing this scope (modules have no enclosing scope) */
    Scope getEnclosingScope() {
        none()
    }

    /** Gets the statements forming the body of this scope */
    StmtList getBody() {
        none()
    }

    /** Gets the nth statement of this scope */
    Stmt getStmt(int n) {
        none()
    }

    /** Gets a top-level statement in this scope */
    Stmt getAStmt() {
        none()
    }

    Location getLocation() {
        none()
    }

    /** Gets the name of this scope */
    string getName() {
        py_strs(result, this, 0)
    }

    /** Gets the docstring for this scope */
    StrConst getDocString() {
        result = ((ExprStmt)this.getStmt(0)).getValue()
    }

    /** Gets the entry point into this Scope's control flow graph */
    ControlFlowNode getEntryNode() {
        py_scope_flow(result, this, -1)
    }

    /** Gets the non-explicit exit from this Scope's control flow graph */
    ControlFlowNode getFallthroughNode() {
        py_scope_flow(result, this, 0)
    }

    /** Gets the exit of this scope following from a return statement */
    ControlFlowNode getReturnNode() {
        py_scope_flow(result, this, 2)
    }

    /** Gets an exit from this Scope's control flow graph */
    ControlFlowNode getAnExitNode() {
	      exists (int i | py_scope_flow(result, this, i) and i >= 0)
    }

    /** Gets an exit from this Scope's control flow graph,
     *  that does not result from an exception */
    ControlFlowNode getANormalExit() {
        result = this.getFallthroughNode()
        or
        result = this.getReturnNode()
    }

    /** Whether this a top-level (non-nested) class or function */
    predicate isTopLevel() {
        this.getEnclosingModule() = this.getEnclosingScope()
    }

    /** Whether this scope is deemed to be public */
    predicate isPublic() {
        /* Not inside a function */
        not this.getEnclosingScope() instanceof Function and
        /* Not implicitly private */
        this.getName().charAt(0) != "_" and
        (
            this instanceof Module 
            or
            exists(Module m | 
                m = this.getEnclosingScope() and m.isPublic() |
                /* If the module has an __all__, is this in it */
                not exists(m.getAnExport())
                or
                m.getAnExport() = this.getName()
            )
            or
            exists(Class c | c = this.getEnclosingScope() |
                this instanceof Function and
                c.isPublic()
            )
        )
    }

    predicate contains(Stmt s) {
        this.getBody().contains(s)
        or
        exists(Scope inner | inner.getEnclosingScope() = this | inner.contains(s))
    }

    /** Whether this scope (immediately) precedes the other.
     * That is, is it impossible for other to execute without
     * this having executed at least once and of those scopes
     * which must precede this scope, `other` is the most immediate.
     */
    predicate precedes(Scope other) {
        final_scope_precedes(this, other, _)
    }

    /** Gets the evaluation scope for code in this (lexical) scope.
     * This is usually the scope itself, but may be an enclosing scope.
     * Notably, for list comprehensions in Python 2.
     */
    Scope getEvaluatingScope() {
        result = this
    }

}
