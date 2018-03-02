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

abstract class BaseWebobRequest extends TaintKind {

    bindingset[this]
    BaseWebobRequest() { any() }

    override TaintKind getTaintOfAttribute(string name) {
        result instanceof ExternalStringDictKind and
        (
            name = "GET" or
            name = "POST" or
            name = "headers"
        )
        or
        result instanceof ExternalStringKind and
        (
            name = "body"
        )
    }

    override TaintKind getTaintOfMethodResult(string name) {
        result = this and
        (
            name = "copy" or
            name = "copy_get" or
            name = "copy_body"
        )
        or
        result instanceof ExternalStringKind and 
        (
            name = "as_bytes"
        )
    }

}

class WebobRequest extends BaseWebobRequest {

    WebobRequest() {
        this = "webob.Request"
    }

    ClassObject getClass() {
        exists(ModuleObject req |
            req.getName() = "webob.request" and
            result = req.getAttribute("Request")
        )
    }

}
