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
 * @name Passing sensitive information in a URL
 * @description Encoding sensitive information in a URL is insecure
 *              because the URL can be logged.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/sensitive-information-in-url
 * @tags security
 *       external/cwe/cwe-319
 */

import cpp

/**
 * An expression that sends an Objective C message to
 * `NSURL::+URLWithString:`.
 */
class CreateNSURL extends MessageExpr {
  CreateNSURL() {
    getStaticTarget().hasQualifiedName("NSURL::+URLWithString:")
  }
}

/**
 * Gets an expression that may have been used when computing `expr`'s
 * value.
 */
Expr sourceExpr(Expr expr) {
  result = expr or
  result = sourceExpr(expr.getAChild+()) or
  exists(Variable v | v.getAnAccess() = expr
                    | result = sourceExpr(v.getAnAssignedValue()))
}

/** Holds if `expr` looks like it contains sensitive information. */
predicate sensitiveExpr(Expr expr) {
  expr.toString().toLowerCase().matches(sensitiveMatch())
}

/**
 * Holds if `expr` looks like it contains encrypted or hashed
 * information.
 */
predicate nonsensitiveExpr(Expr expr) {
  expr.toString().toLowerCase().matches(nonsensitiveMatch())
}

/** Gets a pattern used to recognize sensitive information. */
string sensitiveMatch() {
  result = "%pass%" or
  result = "%token%" or
  result = "%key%" or
  result = "%account%" or
  result = "%accnt%"
}

/** Gets a pattern used to recognize encrypted or hashed information. */
string nonsensitiveMatch() {
  result = "%hash%" or
  result = "%crypt%"
}

from CreateNSURL url, Expr sensitive
where sensitive = sourceExpr(url)
  and sensitiveExpr(sensitive)
  and not nonsensitiveExpr(sourceExpr(url))
select url, "URL contains potentially $@", sensitive, "sensitive data"
