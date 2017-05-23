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
 * @name Unused variable
 * @description Unused variables may be a symptom of a bug and should be examined carefully.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 * @precision very-high
 */

import javascript

/**
 * A local variable that is neither used nor exported, and is not a parameter
 * or a function name.
 */
class UnusedLocal extends LocalVariable {
  UnusedLocal() {
    not exists(getAnAccess()) and
    not exists(Parameter p | this = p.getAVariable()) and
    not exists(FunctionExpr fe | this = fe.getVariable()) and
    not exists(ExportNamedDeclaration end | this = end.getADecl().getVariable())
  }
}

/**
 * Holds if `v` is mentioned in a JSDoc comment in the same file, and that file
 * contains externs declarations.
 */
predicate mentionedInJSDocComment(UnusedLocal v) {
  exists (Externs ext, JSDoc jsdoc |
    ext = v.getADeclaration().getTopLevel() and jsdoc.getComment().getTopLevel() = ext |
    jsdoc.getComment().getText().regexpMatch("(?s).*\\b" + v.getName() + "\\b.*")
  )
}

/**
 * Holds if `v` is declared in an object pattern that also contains a rest pattern.
 *
 * This is often used to filter out properties; for example, `var { x: v, ...props } = o`
 * copies all properties of `o` into `props`, except for `x` which is copied into `v`.
 */
predicate isPropertyFilter(UnusedLocal v) {
  exists (ObjectPattern op | exists(op.getRest()) |
    op.getAPropertyPattern().getValuePattern() = v.getADeclaration()
  )
}

/**
 * Holds if `v` is an import of React, and there is a JSX element that implicitly
 * references it.
 */
predicate isReactImportForJSX(UnusedLocal v) {
  exists (ImportSpecifier is |
    is.getLocal() = v.getADeclaration() and
    exists (JSXElement jsx | jsx.getTopLevel() = is.getTopLevel()) |
    v.getName() = "React" or
    // also accept legacy `@jsx` pragmas
    exists (JSXPragma p | p.getTopLevel() = is.getTopLevel() | p.getDOMName() = v.getName())
  )
}

from VarDecl vd, UnusedLocal v
where v = vd.getVariable() and
      // exclude variables mentioned in JSDoc comments in externs
      not mentionedInJSDocComment(v) and
      // exclude variables used to filter out unwanted properties
      not isPropertyFilter(v) and
      // exclude imports of React that are implicitly referenced by JSX
      not isReactImportForJSX(v)
select vd, "Unused variable " + v + "."