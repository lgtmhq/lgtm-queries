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
 * Library for detecting pairs of identical AST subtrees.
 */

import javascript

/**
 * Helper function for encoding the type of an AST node as
 * an integer.
 *
 * Note that every AST node has exactly one kind.
 */
private int kindOf(ASTNode nd) {
  // map expression kinds to even non-negative numbers
  result = nd.(Expr).getKind() * 2 or
  // map statement kinds to odd non-negative numbers
  result = nd.(Stmt).getKind() * 2 + 1 or
  // other node types get negative kinds
  nd instanceof TopLevel and result = -1 or
  nd instanceof Property and result = -2 or
  nd instanceof Class    and result = -3
}

/**
 * Associate AST nodes with their literal value, if they have one.
 * For identifiers, we consider the name to be their value.
 *
 * Note that every AST node has at most one value.
 */
private string valueOf(ASTNode nd) {
  result = nd.(Literal).getRawValue() or
  result = nd.(TemplateElement).getRawValue() or
  result = nd.(Identifier).getName()
}

/**
 * A base class for doing structural comparisons of program elements.
 * 
 * Clients are must override the `candidate()` method to identify the
 * nodes for which structural comparison will be interesting.
 */
abstract class StructurallyCompared extends ASTNode {
  /**
   * Get a candidate node that we may want to structurally compare this node to.
   */
  abstract ASTNode candidate();

  /**
   * A predicate that recursively extends `candidate()` to also take corresponding
   * children into account.
   */
  ASTNode candidateInternal() {
    // in order to correspond, nodes need to have the same kind and shape
    kindOf(this) = kindOf(result) and this.getNumChild() = result.getNumChild() and
    (result = candidate() or
     exists (int i | result = getAStructuralUncle(i).getChild(i)))
  }

  /**
   * If this node is the i-th child of a node that is also structurally
   * compared, then the results of this predicate are all nodes corresponding
   * to that parent node.
   */
  private ASTNode getAStructuralUncle(int i) {
    exists (StructurallyCompared parent | this = parent.getChild(i) |
      result = parent.candidateInternal()
    )
  }

  /**
   * Do structural equality on all nodes that are potentially relevant to the
   * comparison.
   *
   * This reports equality on all nodes that correspond via `candidateInternal()`.
   */
  private predicate sameInternal(ASTNode that) {
    that = this.candidateInternal() and

    /* Check that `this` and `that` bind to the same variable, if any.
     * Note that it suffices to check the implication one way: since we restrict
     * `this` and `that` to be of the same kind and in the same syntactic
     * position, either both bind to a variable or neither does. */
    (bind(this, _) implies exists(Variable v | bind(this, v) and bind(that, v))) and

    /* Check that `this` and `that` have the same constant value, if any.
     * As above, it suffices to check one implication. */
    (exists(valueOf(this)) implies valueOf(this) = valueOf(that)) and

    forall (StructurallyCompared child, int i |
       child = getChild(i) and that = child.getAStructuralUncle(i) |
       child.sameInternal(that.getChild(i))
    )
  }

  /**
   * Compare this node structurally to a candidate node.
   */
  predicate same(ASTNode that) {
    that = this.candidate() and
    this.sameInternal(that)
  }
}

/**
 * Helper class for marking children of nodes that are comparison
 * candidates to themselves be comparison candidates.
 */
library class InternalCandidate extends StructurallyCompared {
  InternalCandidate() {
    exists (getParent().(StructurallyCompared).candidateInternal())
  }

  ASTNode candidate() { none() }
}

/**
 * Clone detector for finding comparisons where both operands are the same.
 */
class OperandComparedToSelf extends StructurallyCompared {
  OperandComparedToSelf() {
    exists (Comparison comp | this = comp.getLeftOperand())
  }

  Expr candidate() {
    result = getParent().(Comparison).getRightOperand()
  }
}

/**
 * Clone detector for finding assignments where lhs and rhs are the same.
 */
class SelfAssignment extends StructurallyCompared {
  SelfAssignment() {
    exists (AssignExpr assgn | this = assgn.getLhs())
  }

  Expr candidate() {
    result = getParent().(AssignExpr).getRhs()
  }
}

/**
 * Clone detector for finding structurally identical property initialisers.
 */
class DuplicatePropertyInitDetector extends StructurallyCompared {
  DuplicatePropertyInitDetector() {
    exists (ObjectExpr oe, string p |
      this = oe.getPropertyByName(p).getInit() and
      oe.getPropertyByName(p) != oe.getPropertyByName(p)
    )
  }

  Expr candidate() {
    exists (ObjectExpr oe, string p |
      this = oe.getPropertyByName(p).getInit() and
      result = oe.getPropertyByName(p).getInit() and
      result != this
    )
  }
}
