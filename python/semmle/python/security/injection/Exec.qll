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

/** Provides class and predicates to track external data that
 * may represent malicious Python code.
 *
 * This module is intended to be imported into a taint-tracking query
 * to extend `TaintKind` and `TaintSink`.
 *
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Untrusted


private FunctionObject exec_or_eval() {
    result = builtin_object("exec")
    or
    result = builtin_object("eval")
}

/** A taint sink that represents an argument to exec or eval that is vulnerable to malicious input.
 * The `vuln` in `exec(vuln)` or similar.
 */
class StringEvaluationNode extends TaintSink {

    string toString() { result = "exec or eval" }

    StringEvaluationNode() {
        exists(Exec exec |
            exec.getASubExpression().getAFlowNode() = this
        )
        or
        exists(CallNode call |
            exec_or_eval().getACall() = call and
            call.getAnArg() = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}
