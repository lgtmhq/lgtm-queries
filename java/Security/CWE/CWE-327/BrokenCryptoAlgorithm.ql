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
 * @name Use of a broken or risky cryptographic algorithm
 * @description Using broken or weak cryptographic algorithms can allow an attacker to compromise security.
 * @kind problem
 * @problem.severity error
 * @cwe 327
 */
import default
import semmle.code.java.security.Encryption
import semmle.code.java.security.DataFlow

class BrokenAlgoLiteral extends FlowSource {
  BrokenAlgoLiteral() {
    this.(StringLiteral).getLiteral().regexpMatch(algorithmBlacklistRegex())
  }
}

from CryptoAlgoSpec c, Expr a, BrokenAlgoLiteral s
where a = c.getAlgoSpec() and
      s.flowsTo(a)
select c, "Cryptographic algorithm $@ is weak and should not be used.",
  s, s.(StringLiteral).getLiteral()
