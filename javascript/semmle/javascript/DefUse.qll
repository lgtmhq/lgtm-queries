// Copyright 2016 Semmle Ltd.
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

import Expr
import Stmt

/**
 * A CFGNode that defines (i.e., initializes or updates) a variable.
 *
 * <p>
 * The following program elements perform variable updates:
 * </p>
 *
 * <ul>
 * <li>assignment expressions</li>
 * <li>update expressions</li>
 * <li>variable declarators with an initializer</li>
 * <li>for-in and for-of statements</li>
 * <li>function declaration statements</li>
 * <li>function calls</li>
 * <li>catch blocks</li>
 * </ul>
 */
class VarDef extends CFGNode {
  VarDef() {
    // an assignment (simple or compound)
    this instanceof Assignment or
    // an increment/decrement expression
    this instanceof UpdateExpr or
    // a variable declaration with an initializer
    exists (this.(VariableDeclarator).getInit()) or
    // the iterator of a for-in/for-of statement
    exists (EnhancedForLoop fl | this = fl.getIteratorExpr()) or
    // a parameter of a function or catch clause
    this instanceof Parameter or
    // a function identifier
    exists (Function fn | this = fn.getId()) or
    // a class identifier
    exists (ClassDefinition cd | this = cd.getIdentifier()) or
    // a comprehension block
    exists (ComprehensionBlock cb | this = cb.getIterator()) or
    // an import
    this instanceof ImportSpecifier
  }

  /**
   * Get the target of this definition, which is either a simple variable
   * reference, or a more complex destructuring pattern.
   */
  BindingPattern getTarget() {
    result = this.(Assignment).getTarget() or
    result = this.(UpdateExpr).getOperand().stripParens() or
    result = this.(VariableDeclarator).getBindingPattern() or
    result = this.(ImportSpecifier).getLocal() or
    result = this
  }

  /** Get a variable defined by this node. */
  Variable getAVariable() {
    result = getTarget().getAVariable()
  }

  /**
   * If this definition assigns an expression to a single variable,
   * return that expression.
   */
  Expr getSource() {
    exists (VariableDeclarator vd | vd = this and vd.getBindingPattern() instanceof VarDecl |
      result = vd.getInit()
    ) or
    exists (FunctionExpr fe | fe.getId() = this | result = fe) or
    exists (ClassExpr ce | ce.getIdentifier() = this | result = ce) or
    exists (AssignExpr assgn | this = assgn and assgn.getTarget() instanceof VarAccess |
      result = assgn.getRhs()
    )
  }
}

/**
 * A CFGNode that uses a variable.
 *
 * <p>
 * Some variable definitions are also uses, notably the operands of update expressions.
 * </p>
 */
class VarUse extends CFGNode {
  VarUse() {
    this instanceof VarAccess and
    not exists (AssignExpr assgn | assgn.getTarget() = this) and
    not exists (EnhancedForLoop ef | ef.getIterator() = this) and
    not exists (DestructuringPattern p | this = p.getABindingVarRef())
  }

  /** Get the variable this use refers to. */
  Variable getVariable() {
    result = this.(VarAccess).getVariable()
  }

  /**
   * A definition that may reach this use.
   *
   * For global variables and variables that are captured in a closure, each definition is
   * considered to reach each use.
   */
  VarDef getADef() {
    localDefinitionReaches(_, result, this) or
    exists (Variable v | v.isGlobal() or v.isCaptured() |
      v = getVariable() and
      result.getAVariable() = v
    )
  }
}

/**
 * Does the definition of `v` in `def` reach `use` along some control flow path
 * without crossing another definition of `v`? 
 */
predicate definitionReaches(Variable v, VarDef def, VarUse use) {
  v = use.getVariable() and
  exists (BasicBlock bb, int i, int next | next = nextDefAfter(bb, v, i, def) |
    exists (int j | j in [i+1..next-1] | bb.useAt(j, v, use)) or
    exists (BasicBlock succ | succ = bb.getASuccessor() |
      succ.isLiveAtEntry(v, use) and
      next = bb.length()
    )
  )
}

/**
 * Alternative implementation of `definitionReaches` for purely local variables.
 */
predicate localDefinitionReaches(PurelyLocalVariable v, VarDef def, VarUse use) {
  v = use.getVariable() and
  exists (BasicBlock bb, int i, int next | next = nextDefAfter(bb, v, i, def) |
    exists (int j | j in [i+1..next-1] | bb.useAt(j, v, use)) or
    exists (BasicBlock succ | succ = bb.getASuccessor() |
      succ.localIsLiveAtEntry(v, use) and
      next = bb.length()
    )
  )
}

/**
 * For a definition `d` of `v` at index `i` in `bb`, get the next index in `bb` after
 * `i` at which the same variable is defined, or `bb.length()` if there is none.
 */
private int nextDefAfter(BasicBlock bb, Variable v, int i, VarDef d) {
  bb.defAt(i, v, d) and
  result = min(int jj | (bb.defAt(jj, v, _) or jj = bb.length()) and jj > i)
}

/**
 * Could the `later` definition of `v` overwrite its `earlier` definition?
 *
 * This is the case if there is a path from `earlier` to `later` that does not cross
 * another definition of `v`.
 */
predicate localDefinitionOverwrites(PurelyLocalVariable v, VarDef earlier, VarDef later) {
  exists (BasicBlock bb, int i, int next | next = nextDefAfter(bb, v, i, earlier) |
    bb.defAt(next, v, later) or
    exists (BasicBlock succ | succ = bb.getASuccessor() |
      succ.localMayBeOverwritten(v, later) and
      next = bb.length()
    )
  )
}
