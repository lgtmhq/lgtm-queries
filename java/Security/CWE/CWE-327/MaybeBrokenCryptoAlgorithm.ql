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
import semmle.code.java.dispatch.VirtualDispatch

private class ShortStringLiteral extends StringLiteral {
  ShortStringLiteral() {
    getLiteral().length() < 100
  }
}

class InsecureAlgoLiteral extends ShortStringLiteral {
  InsecureAlgoLiteral() {
    // Algorithm identifiers should be at least two characters.
    getValue().length() > 1 and
    exists(string s | s = getLiteral() |
      not s.regexpMatch(algorithmWhitelistRegex())
      // Exclude results covered by another query.
      and not s.regexpMatch(algorithmBlacklistRegex())
    )
  }
}

predicate initialFlow(InsecureAlgoLiteral s, Node n) {
  TaintTracking::localTaint(exprNode(s), n) and
  (
    exists(CryptoAlgoSpec c | n.asExpr() = c.getAlgoSpec()) or
    localFlowExit(n)
  )
}

predicate objectToString(MethodAccess ma) {
  exists(Method m |
    m = ma.getMethod() and
    m.hasName("toString") and
    m.getDeclaringType() instanceof TypeObject and
    variableTrack(ma.getQualifier()).getType().getErasure() instanceof TypeObject
  )
}

class StringContainer extends RefType {
  StringContainer() {
    this instanceof TypeString or
    this.hasQualifiedName("java.lang", "StringBuilder") or
    this.hasQualifiedName("java.lang", "StringBuffer") or
    this.hasQualifiedName("java.util", "StringTokenizer") or
    this.(Array).getComponentType() instanceof StringContainer
  }
}

class InsecureCryptoConfiguration extends TaintTracking::Configuration {
  InsecureCryptoConfiguration() { this = "InsecureCryptoConfiguration" }
  override predicate isSource(Node n) {
    initialFlow(_, n)
  }
  override predicate isSink(Node n) {
    exists(CryptoAlgoSpec c | n.asExpr() = c.getAlgoSpec())
  }
  override predicate isSanitizer(Node n) {
    objectToString(n.asExpr()) or
    not n.getType().getErasure() instanceof StringContainer
  }
}

from CryptoAlgoSpec c, Expr a, InsecureAlgoLiteral s, Node n, InsecureCryptoConfiguration conf
where
  a = c.getAlgoSpec() and
  initialFlow(s, n) and
  conf.hasFlow(n, exprNode(a))
select c, "Cryptographic algorithm $@ may not be secure, consider using a different algorithm.",
  s, s.getLiteral()
