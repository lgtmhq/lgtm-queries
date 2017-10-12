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
 * @name Use of a potentially broken or risky cryptographic algorithm
 * @description Using broken or weak cryptographic algorithms can allow an attacker to compromise security.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/potentially-weak-cryptographic-algorithm
 * @tags security
 *       external/cwe/cwe-327
 */
import java
import semmle.code.java.security.Encryption
import semmle.code.java.dataflow.TaintTracking
import DataFlow

private class ShortStringLiteral extends StringLiteral {
  ShortStringLiteral() {
    getLiteral().length() < 100
  }
}

class InsecureAlgoLiteral extends ShortStringLiteral {
  InsecureAlgoLiteral() {
    exists(string s | s = getLiteral() |
      not s.regexpMatch(algorithmWhitelistRegex())
      // Exclude results covered by another query.
      and not s.regexpMatch(algorithmBlacklistRegex())
    )
  }
}

class InsecureCryptoConfiguration extends TaintTracking::Configuration {
  InsecureCryptoConfiguration() { this = "InsecureCryptoConfiguration" }
  override predicate isSource(Node n) {
    n.asExpr() instanceof InsecureAlgoLiteral
  }
  override predicate isSink(Node n) {
    exists(CryptoAlgoSpec c | n.asExpr() = c.getAlgoSpec())
  }
}

from CryptoAlgoSpec c, Expr a, InsecureAlgoLiteral s, InsecureCryptoConfiguration conf
where
  a = c.getAlgoSpec() and
  conf.hasFlow(exprNode(s), exprNode(a))
select c, "Cryptographic algorithm $@ may not be secure, consider using a different algorithm.",
  s, s.getLiteral()
