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
 * @name Unused parameter
 * @description Unused parameters make functions hard to read and hard to use, and should be removed.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 */

import javascript

/**
 * Could `f` be used as a higher-order function, i.e., passed as a callback or
 * assigned to a property?
 *
 * This predicate is deliberately overapproximate: it holds for many functions that
 * are not actually higher-order, but any function for which it does not hold can safely
 * be assumed to be first-order (modulo `eval` and the usual corner cases).
 */
predicate isHigherOrder(Function f) {
  // check whether there is a use of `f` that is not a call
  exists (Expr use | use = f.getVariable().getAnAccess() or use = f |
    not exists (InvokeExpr invk | use = invk.getCallee().stripParens())
  )
}

/**
 * Check whether p, the i-th parameter of f, is unused.
 */
predicate isUnused(Function f, Parameter p, Variable pv, int i) {
  p = f.getParameter(i) and
  pv = p.getAVariable() and
  // p is not accessed directly
  not exists(pv.getAnAccess()) and
  // nor could it be accessed through arguments
  not f.usesArgumentsObject()
}

from Function f, Parameter p, Variable pv, int i
where isUnused(f, p, pv, i) and
      (// either f is first-order (so its parameter list is easy to adjust), or
       not isHigherOrder(f) or
       // p is a destructuring parameter, or
       not p instanceof SimpleParameter or
       // every later parameter is non-destructuring and also unused
       forall (Parameter q, int j | q = f.getParameter(j) and j > i | isUnused(f, q.(SimpleParameter), _, _))) and
      // f is not an extern
      not f.inExternsFile() and
      // and p is not documented as being unused
      not exists (JSDocParamTag parmdoc | parmdoc.getDocumentedParameter() = pv |
        parmdoc.getDescription().toLowerCase().matches("%unused%")
      ) and
      // and f is not marked as abstract
      not f.getDocumentation().getATag().getTitle() = "abstract" and
      // this case is checked by a different query
      not f.(FunctionExpr).isSetter() and
      // `p` isn't used in combination with a rest property pattern to filter out unwanted properties
      not exists (ObjectPattern op | exists(op.getRest()) |
        op.getAPropertyPattern().getValuePattern() = pv.getADeclaration()
      )
select p, "Unused parameter " + pv.getName() + "."