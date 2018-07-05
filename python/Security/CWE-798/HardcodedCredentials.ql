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
 * @name Hard-coded credentials
 * @description Credentials are hard coded in the source code of the application.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @id py/hardcoded-credentials
 * @tags security
 *       external/cwe/cwe-259
 *       external/cwe/cwe-321
 *       external/cwe/cwe-798
 */

import semmle.python.security.TaintTracking
import semmle.python.filters.Tests

class HardcodedValue extends TaintKind {

    HardcodedValue() {
        this = "hard coded value"
    }

}

class HardcodedValueSource extends TaintSource {

    HardcodedValueSource() {
        /* At least 5 characters */
        this.(ControlFlowNode).getNode().(StrConst).getText().length() > 4
        or
        exists(IntegerLiteral lit |
            this.(ControlFlowNode).getNode() = lit
            |
            /* or, at least 8 digits */
            not exists(lit.getValue())
            or
            lit.getValue() > 10000000
        )
    }

    override predicate isSourceOf(TaintKind kind) {
        kind instanceof HardcodedValue
    }

}

class CredentialSink extends TaintSink {

    CredentialSink() {
        exists(string name |
            name.regexpMatch(getACredentialRegex()) and
            not name.suffix(name.length()-4) = "file"
            |
            any(FunctionObject func).getNamedArgumentForCall(_, name) = this
            or
            exists(Keyword k |
                k.getArg() = name and k.getValue().getAFlowNode() = this
            )
            or
            exists(CompareNode cmp, NameNode n |
                n.getId() = name
                |
                cmp.operands(this, any(Eq eq), n)
                or
                cmp.operands(n, any(Eq eq), this)
            )
        )
    }


    override predicate sinks(TaintKind kind) {
        kind instanceof HardcodedValue
    }

}

/**
  * Gets a regular expression for matching names of locations (variables, parameters, keys) that
  * indicate the value being held is a credential.
  */
private string getACredentialRegex() {
  result = "(?i).*pass(wd|word|code|phrase)(?!.*question).*" or
  result = "(?i).*(puid|username|userid).*" or
  result = "(?i).*(cert)(?!.*(format|name)).*"
}

from TaintSource src, TaintSink sink

where src.flowsToSink(sink) and
not any(TestScope test).contains(src.(ControlFlowNode).getNode())

select sink, "Use of hardcoded credentials from $@.", src, src.toString()
