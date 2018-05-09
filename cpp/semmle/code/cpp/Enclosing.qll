// Copyright 2018 Semmle Ltd.
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

import cpp

/**
 * Gets the enclosing element of statement `s`.
 */
Element stmtEnclosingElement(Stmt s) {
  result.(Function).getEntryPoint() = s or
  result = stmtEnclosingElement(s.getParent()) or
  result = exprEnclosingElement(s.getParent())
}

/**
 * Gets the enclosing element of expression `e`.
 */
Element exprEnclosingElement(Expr e) {
  result = exprEnclosingElement(e.getParent()) or
  result = stmtEnclosingElement(e.getParent()) or
  result.(Function) = e.getParent() or
  result = exprEnclosingElement(e.(Conversion).getExpr()) or
  exists(Initializer i | i.getExpr() = e and
                         if exists(i.getEnclosingStmt())
                         then result = stmtEnclosingElement(i.getEnclosingStmt())
                         else if i.getDeclaration() instanceof Parameter
                         then result = i.getDeclaration().(Parameter).getFunction()
                         else result = i.getDeclaration()) or
  exists(Expr anc | expr_ancestor(e, anc) and result = exprEnclosingElement(anc)) or
  exists(Stmt anc | expr_ancestor(e, anc) and result = stmtEnclosingElement(anc)) or
  exists(DeclarationEntry de |
         expr_ancestor(e, de) and
         if exists(DeclStmt ds | de = ds.getADeclarationEntry())
         then exists(DeclStmt ds |
                     de = ds.getADeclarationEntry() and
                     result = stmtEnclosingElement(ds))
         else result = de.getDeclaration())
}

