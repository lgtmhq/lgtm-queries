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

/**
 * @name Use of a broken or risky cryptographic algorithm
 * @description Using broken or weak cryptographic algorithms can allow
 *              an attacker to compromise security.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @id cpp/weak-cryptographic-algorithm
 * @tags security
 *       external/cwe/cwe-327
 */
import cpp
import semmle.code.cpp.security.Encryption

abstract class InsecureCryptoSpec extends Locatable {
  abstract string description();
}

class InsecureFunctionCall extends InsecureCryptoSpec, FunctionCall {
  InsecureFunctionCall() {
    this.getTarget().getName().regexpMatch(algorithmBlacklistRegex())
  }

  override string description() { result = "function call" }

  override string toString() { result = FunctionCall.super.toString() }
  override Location getLocation() { result = FunctionCall.super.getLocation() }
}

class InsecureMacroSpec extends InsecureCryptoSpec, MacroInvocation {
  InsecureMacroSpec() {
    this.getMacro().getName().regexpMatch(algorithmBlacklistRegex())
  }

  override string description() { result = "macro invocation" }

  override string toString() { result = MacroInvocation.super.toString() }
  override Location getLocation() { result = MacroInvocation.super.getLocation() }
}

from InsecureCryptoSpec c
select c, "This " + c.description() + " specifies a broken or weak cryptographic algorithm."
