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
 * may represent malicious marshals.
 *
 * This module is intended to be imported into a traint-tracking query
 * to extend `TaintKind` and `TaintSink`.
 *
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Untrusted


private FunctionObject marshalLoads() {
    result = any(ModuleObject marshal | marshal.getName() = "marshal").getAttribute("loads")
}


/** A taint sink that is potentially vulnerable to malicious marshaled objects.
 * The `vuln` in `marshal.loads(vuln)`. */
class UnmarshalingNode extends TaintSink {

    string toString() { result = "unmarshaling vulnerability" }

    UnmarshalingNode() {
        exists(CallNode call |
            marshalLoads().getACall() = call and
            call.getAnArg() = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}
