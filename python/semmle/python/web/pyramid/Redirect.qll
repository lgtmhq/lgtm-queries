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

/** Provides class representing the `pyramid.redirect` function.
 * This module is intended to be imported into a taint-tracking query
 * to extend `TaintSink`.
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Basic


private ClassObject redirectClass() {
    exists(ModuleObject ex |
        ex.getName() = "pyramid.httpexceptions" |
        ex.getAttribute("HTTPFound") = result
        or
        ex.getAttribute("HTTPTemporaryRedirect") = result
    )
}

/**
 * Represents an argument to the `tornado.redirect` function.
 */
class PyramidRedirect extends TaintSink {

    string toString() {
        result = "pyramid.redirect"
    }

    PyramidRedirect() {
        exists(CallNode call |
            call.getFunction().refersTo(redirectClass()) 
            |
            call.getArg(0) = this
            or
            call.getArgByName("location") = this
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}
