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
 * @name Use of HTTP
 * @description Using the HTTP protocol transmits data insecurely,
 *              allowing it to be intercepted by an attacker.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/use-of-http
 * @tags security
 *       external/cwe/cwe-319
 */

import cpp

/** A variable with type `NSURLRequest *` or `NSMutableURLRequest *`. */
class NSURLRequestVariable extends Variable {
  NSURLRequestVariable() {
    exists(Type t |
      t = this.getUnderlyingType().(PointerType).getBaseType() and
      (t.hasName("NSMutableURLRequest") or t.hasName("NSURLRequest")) )
  }
}

/**
 * Gets all string literals used directly or indirectly in this
 * expression.
 */
string expressionUsesString(Expr expr) {
  result = expr.(TextLiteral).getValue() or
  result = expressionUsesString(expr.getAChild+()) or
  exists(Variable v |
         expr = v.getAnAccess() and
         result = expressionUsesString(v.getAnAssignedValue()))
}

/** Gets all string literals used in this variable. */
string variableUsesString(Variable v) {
  result = expressionUsesString(v.getInitializer().getExpr()) or
  result = expressionUsesString(v.getAnAccess()) or
  result = expressionUsesString(v.getAnAssignment())
}

from NSURLRequestVariable request, string url, string description
where url = variableUsesString(request)
  and (
        (url = "http" and description = "Making HTTP request") or
        (url.matches("http://%") and
         description = "Making HTTP request to address '" + url + "'")
      )
  and not url.matches("%/localhost%")
select request, description
