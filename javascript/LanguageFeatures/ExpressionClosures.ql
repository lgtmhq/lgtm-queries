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
 * @name Use of platform-specific language features
 * @description Non-standard language features such as expression closures or let expressions
 *              make it harder to reuse code.
 * @kind problem
 * @problem.severity warning
 * @tags portability
 *       maintainability
 *       language-features
 */

import javascript

predicate deprecated_feature(ASTNode nd, string type, string replacement) {
  exists (FunctionExpr fe | fe = nd and fe.getBody() instanceof Expr |
    type = "expression closures" and replacement = "arrow expressions"
  ) or
  nd instanceof LegacyLetExpr and type = "let expressions" and replacement = "let declarations" or
  nd instanceof LegacyLetStmt and type = "let statements" and replacement = "let declarations" or
  nd instanceof ForEachStmt and type = "for each statements" and replacement = "for of statements" or
  nd.(ComprehensionExpr).isPostfix() and type = "postfix comprehensions" and replacement = "prefix comprehensions" or
  nd.(ExprStmt).isDoubleColonMethod(_, _, _) and type = "double colon method declarations" and replacement = "standard method definitions"
}

from ASTNode depr, string type, string replacement
where deprecated_feature(depr, type, replacement)
select depr, "Use " + replacement + " instead of " + type + "."