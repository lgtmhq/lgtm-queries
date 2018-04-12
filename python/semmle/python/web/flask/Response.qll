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

import semmle.python.web.flask.General

/** A flask response, which is vulnerable to any sort of 
 * http response malice. */
class FlaskRoutedResponse extends TaintSink {

    FlaskRoutedResponse() {
        exists(PyFunctionObject response |
            flask_routing(_, response.getFunction()) and
            this = response.getAReturnedNode()
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

    string toString() {
        result = "flask.routed.response"
    }

}


class FlaskResponseArgument extends TaintSink {

    FlaskResponseArgument() {
        exists(CallNode call |
            call.getFunction().refersTo(theReponseClass()) and
            call.getArg(0) = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

    string toString() {
        result = "flask.response.argument"
    }

}