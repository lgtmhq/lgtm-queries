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

/** Syntactic node (Class, Function, Module, Expr, Stmt or Comprehension) corresponding to a flow node */
abstract class AstNode extends AstNode_ {

    /** Gets the scope that this node occurs in */
    abstract Scope getScope();

    /** Gets a flow node corresponding to this node */
    ControlFlowNode getAFlowNode() {
        py_flow_bb_node(result, this, _, _)
    }

    /** Gets the location for this AST node */
    Location getLocation() {
        none()
    }

    /** Whether this syntactic element is artificial, that is it is generated 
     *  by the compiler and is not present in the source */
    predicate isArtificial() {
        none()
    }

    /** Gets a child node of this node in the AST. This predicate exists to aid exploration of the AST
      * and other experiments. The child-parent relation may not be meaningful. 
      * For a more meaningful relation in terms of dependency use 
      * Expr.getASubExpression(), Stmt.getASubStatement(), Stmt.getASubExpression() or
      * Scope.getAStmt().
      */
    abstract AstNode getAChildNode();

    /** Gets the parent node of this node in the AST. This predicate exists to aid exploration of the AST
      * and other experiments. The child-parent relation may not be meaningful. 
      * For a more meaningful relation in terms of dependency use 
      * Expr.getASubExpression(), Stmt.getASubStatement(), Stmt.getASubExpression() or
      * Scope.getAStmt() applied to the parent.
      */
    AstNode getParentNode() {
        result.getAChildNode() = this
    }

    /** Whether this contains `inner` syntactically */
    predicate contains(AstNode inner) {
        this.getAChildNode+() = inner
    }

    /** Whether this contains `inner` syntactically and `inner` has the same scope as `this` */
    predicate containsInScope(AstNode inner) {
        this.contains(inner) and
        this.getScope() = inner.getScope()
    }

}
