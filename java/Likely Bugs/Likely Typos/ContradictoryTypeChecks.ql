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
 * @name Contradictory type checks
 * @description Contradictory dynamic type checks in `instanceof` expressions
 *              and casts may cause dead code or even runtime errors, and usually
 *              indicate a logic error.
 * @kind problem
 * @problem.severity warning
 */

import java
import semmle.code.java.dataflow.Guards

/**
 * `ioe` is of the form `v instanceof t`.
 */
predicate instanceOfCheck(InstanceOfExpr ioe, Variable v, RefType t) {
  ioe.getExpr().getProperExpr() = v.getAnAccess() and
  ioe.getTypeName().getType().(RefType).getSourceDeclaration() = t
}

/**
 * Immediately before node `n` is executed, `v instanceof r` evaluates to `b`
 * because of a type test performed by expression `reason`.
 */
predicate isInstanceOf(ControlFlowNode n, Variable v, RefType r, boolean b, Expr reason) {
  // `reason` is a `ConditionNode` that ensures `v instanceof r = b`,
  // and there are no redefinitions of `v` between the condition and `n`.
  exists (ConditionNode i |
    reason = i.getCondition() and
    instanceOfCheck(reason, v, r) and
    controlsNodeWithSameVar(i, b, v, n)
  )
}

/** Expression `e` assumes that `v` could be of type `t`. */
predicate requiresInstanceOf(Expr e, Variable v, RefType t) {
  exists (Expr te | t = te.getType().(RefType).getSourceDeclaration() |
    // `e` is a cast to `(t)v`
    exists (CastExpr ce | ce = e | ce.getExpr() = v.getAnAccess() and te = ce) or
    // `e` is `v instanceof t`
    exists (InstanceOfExpr ie | ie = e | ie.getExpr() = v.getAnAccess() and te = ie.getTypeName())
  )
}

from Expr e, Variable v, RefType t, RefType sup, Expr f
where // `e` assumes that `v` could be of type `t`
      requiresInstanceOf(e, v, t) and
      // but `f`, in fact, ensures that `v` is not of type `sup`, which is a supertype of `t`
      sup = t.getASupertype*() and isInstanceOf(e, v, sup, false, f)
select e, "Variable $@ cannot be of type $@ here, since $@ ensures that it is not of type $@.",
          v, v.getName(), t, t.getName(), f, "this expression", sup, sup.getName()
