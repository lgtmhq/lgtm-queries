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
 * @name Expression has no effect
 * @description An expression that has no effect and is used in a void context is most
 *              likely redundant and may indicate a bug.
 * @kind problem
 * @problem.severity warning
 */

import javascript
import DOMProperties
import semmle.javascript.frameworks.xUnit

predicate inVoidContext(Expr e) {
  exists (ExprStmt parent |
    // e is a toplevel expression in an expression statement
    parent = e.getParent() and
    // but it isn't an HTML attribute or a configuration object
    not exists (TopLevel tl | tl = parent.getParent() |
      tl instanceof CodeInAttribute or
      // if the toplevel in its entirety is of the form `({ ... })`,
      // it is probably a configuration object (e.g., a require.js build configuration)
      (tl.getNumChildStmt() = 1 and e.stripParens() instanceof ObjectExpr)
    )
  ) or
  exists (SeqExpr seq, int i, int n |
    e = seq.getOperand(i) and
    n = seq.getNumOperands() |
    i < n-1 or inVoidContext(seq)
  )
}

/**
 * Check whether 'e' is of the form 'x;' or 'e.p;' and has a JSDoc comment containing a tag.
 * In that case, it is probably meant as a declaration and shouldn't be flagged by this query.
 *
 * This will still flag cases where the JSDoc comment contains no tag at all (and hence carries
 * no semantic information), and expression statements with an ordinary (non-JSDoc) comment
 * attached to them.
 */
predicate isDeclaration(Expr e) {
  (e instanceof VarAccess or e instanceof PropAccess) and
  exists (e.getParent().(ExprStmt).getDocumentation().getATag())
}

/**
 * Check whether `name` is potentially a getter.
 */
predicate isGetterProperty(string name) {
  // there is a call of the form `Object.defineProperty(..., name, { get: ..., ... })`
  exists (CallToObjectDefineProperty defProp |
    name = defProp.getPropertyName() and
    exists(defProp.getPropertyDescriptor().(ObjectExpr).getProperty("get"))
  ) or
  // there is an object expression with a getter property `name`
  exists (ObjectExpr obj | obj.getProperty(name) instanceof PropertyGetter)
}

class GetterPropertyAccess extends PropAccess {
  predicate isImpure() {
    isGetterProperty(getPropertyName())
  }
}

from Expr e
where e.isPure() and inVoidContext(e) and
      // disregard pure expressions wrapped in a void(...) 
      not e instanceof VoidExpr and
      // filter out directives
      not e.getParent() instanceof Directive and
      // or about externs
      not e.inExternsFile() and
      // don't complain about declarations
      not isDeclaration(e) and
      // exclude DOM properties, which sometimes have magical auto-update properties
      not isDOMProperty(e.(PropAccess).getPropertyName()) and
      // exclude xUnit.js annotations
      not e instanceof XUnitAnnotation
select e, "This expression has no effect."
