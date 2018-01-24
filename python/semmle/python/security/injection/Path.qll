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

import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Basic

/** A kind of taint representing an externally controlled string containing
 * a potentially malicious path.
 */
class PathInjection extends ExternalStringKind {

    PathInjection() {
        this = "path.injection"
    }

}

/** A taint sink that is vulnerable to malicious paths.
 * The `vuln` in `open(vuln)` and similar.
 */
class OpenNode extends TaintSink {

    string toString() { result = "argument to open()" }

    OpenNode() {
        exists(CallNode call |
            call.getFunction().refersTo(builtin_object("open")) and
            call.getAnArg() = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof PathInjection
    }

}
