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
 * may represent malicious pickles.
 *
 * This module is intended to be imported into a traint-tracking query
 * to extend `TaintKind` and `TaintSink`.
 *
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Untrusted


private ModuleObject pickleModule() {
    result.getName() = "pickle"
    or
    result.getName() = "cPickle"
}

private FunctionObject pickleLoads() {
    result = pickleModule().getAttribute("loads")
}

/** `pickle.loads(untrusted)` vulnerability. */
class UnpicklingNode extends TaintSink {

    string toString() { result = "unpickling untrusted data" }

    UnpicklingNode() {
        exists(CallNode call |
            pickleLoads().getACall() = call and
            call.getAnArg() = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}
