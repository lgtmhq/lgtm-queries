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
import semmle.python.web.Http
private import semmle.python.web.webob.Request
private import semmle.python.web.pyramid.View

class PyramidRequest extends BaseWebobRequest {

    PyramidRequest() {
        this = "pyramid.request"
    }

    override ClassObject getClass() {
        exists(ModuleObject req |
            req.getName() = "pyramid.request" and
            result = req.getAttribute("Request")
        )
    }

}

/** Source of pyramid request objects */
class PyramidViewArgument extends TaintSource {

    PyramidViewArgument() {
        exists(Function view_func |
            is_view_function(view_func) and
            this.(ControlFlowNode).getNode() = view_func.getArg(0)
        )
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof PyramidRequest
    }

    string toString() {
        result = "pyramid.view.argument"
    }

}

