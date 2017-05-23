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
 * @name Non-synchronized override of synchronized method
 * @description If a synchronized method is overridden in a subclass, and the overriding method is
 *              not synchronized, the thread-safety of the subclass may be broken.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @tags reliability
 *       correctness
 *       concurrency
 *       language-features
 *       external/cwe/cwe-820
 */

import java

/**
 * Check whether expression `e` is a call to method `target` of the form
 * `super.m(x, y, z)`, possibly wrapped in one or more casts and/or parentheses.
 */
predicate delegatingSuperCall(Expr e, Method target) {
  exists (MethodAccess call | call = e |
    call.getQualifier() instanceof SuperAccess and
    call.getCallee() = target and
    forall (Expr arg | arg = call.getAnArgument() | arg instanceof VarAccess)
  ) or
  delegatingSuperCall(e.(CastExpr).getExpr(), target) or
  delegatingSuperCall(e.(ParExpr).getExpr(), target)
}

/**
 * Check whether method `sub` is a trivial override of method `sup` that simply
 * delegates to `sup`.
 */
predicate delegatingOverride(Method sub, Method sup) {
  exists (Stmt stmt | 
    // The body of `sub` consists of a single statement...
    stmt = sub.getBody().(SingletonBlock).getStmt() and
    (
      // ...that is either a delegating call to `sup` (with a possible cast)...
      delegatingSuperCall(stmt.(ExprStmt).getExpr(), sup) or
      // ...or a `return` statement containing such a call.
      delegatingSuperCall(stmt.(ReturnStmt).getResult(), sup)
    )
  )
}

from Method sub, Method sup, Class sup_src
where sub.overrides(sup) and
      sub.fromSource() and
      sup.isSynchronized() and
      not sub.isSynchronized() and
      not delegatingOverride(sub, sup) and
      sup_src = sup.getDeclaringType().getSourceDeclaration()
select sub,
  "Method '" + sub.getName() + "' overrides a synchronized method in " +
  sup_src.getQualifiedName() + " but is not synchronized."
