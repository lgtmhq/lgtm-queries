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

/**
 * @name Useless conditional
 * @description If a conditional expression always evaluates to true or always
 *              evaluates to false, this suggests incomplete code or a logic
 *              error.
 * @kind problem
 * @problem.severity warning
 */

import semmle.javascript.flow.Analysis

/**
 * Check whether `va` is a defensive check that may be worth keeping, even if it
 * is strictly speaking useless.
 *
 * We currently recognise three patterns:
 *
 *   - the first `x` in `x || (x = e)`
 *   - the second `x` in `x = (x || e)`
 *   - the second `x` in `var x = x || e`
 */
predicate isDefensiveInit(VarAccess va) {
  exists (LogOrExpr o, VarRef va2 |
    va = o.getLeftOperand().stripParens() and va2.getVariable() = va.getVariable() |
    exists (AssignExpr assgn | va2 = assgn.getTarget() |
      assgn = o.getRightOperand().stripParens() or
      o = assgn.getRhs().stripParens()
    ) or
    exists (VariableDeclarator vd | va2 = vd.getBindingPattern() |
      o = vd.getInit().stripParens()
    )
  )
}

/**
 * Check whether `v` looks like a symbolic constant; we do not consider conditionals
 * to be useless if they check a symbolic constant.
 */
predicate isSymbolicConstant(Variable v) {
  // defined exactly once
  count (VarDef vd | vd.getAVariable() = v) = 1 and
  // the definition is either a `const` declaration or it assigns a constant to it
  exists (VarDef vd | vd.getAVariable() = v and count(vd.getAVariable()) = 1 |
    vd.(VariableDeclarator).getDeclStmt() instanceof ConstDeclStmt or
    isConstant(vd.getSource())
  )
}

/**
 * Check whether `e` is a literal constant or a reference to a symbolic constant.
 */
predicate isConstant(Expr e) {
  e instanceof Literal or
  isSymbolicConstant(e.(VarAccess).getVariable())
}

/**
 * Check whether `e` is an expression that should be whitelisted.
 *
 * We currently whitelist three kinds of expressions:
 *
 *   - constants (including references to literal constants) and their negations
 *   - defensive checks
 */
predicate whitelist(Expr e) {
  isConstant(e) or
  isConstant(e.(LogNotExpr).getOperand()) or
  isDefensiveInit(e)
}

/**
 * Check whether `e` is in a syntactic position where its value is checked for
 * truthiness.
 */
predicate isConditional(Expr e) {
  exists (IfStmt i | e = i.getCondition()) or
  exists (ConditionalExpr c | e = c.getCondition()) or
  exists (LogAndExpr a | e = a.getLeftOperand()) or
  exists (LogOrExpr o | e = o.getLeftOperand())
}

from AnalysedFlowNode cond, boolean cv
where isConditional(cond) and
      cv = cond.getTheBooleanValue()and
      not whitelist(cond)
select cond, "This condition always evaluates to " + cv + "."
