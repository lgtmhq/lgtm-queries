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
import semmle.python.security.strings.Basic
import Tornado

/** A tornado.request.HttpRequest object */
class TornadoRequest extends TaintKind {

    TornadoRequest() {
        this = "tornado.request.HttpRequest"
    }

    override TaintKind getTaintOfAttribute(string name) {
        result instanceof ExternalStringDictKind and
        (
            name = "headers" or
            name = "arguments" or
            name = "cookies"
        )
        or
        result instanceof ExternalStringKind and
        (
            name = "path" or
            name = "query" or
            name = "body"
        )
    }

}


class TornadoRequestSource extends TaintSource {

    TornadoRequestSource() {
        isTornadoRequestHandlerInstance(this.(AttrNode).getObject("request"))
    }

    string toString() {
        result = "Tornado request source"
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof TornadoRequest
    }

}

class TornadoExternalInputSource extends TaintSource {

    TornadoExternalInputSource() {
        exists(string name |
            name = "get_argument" or
            name = "get_query_argument" or
            name = "get_body_argument" or
            name = "decode_argument"
            |
            this = callToNamedTornadoRequestHandlerMethod(name)
        )
    }

    string toString() {
        result = "Tornado request method"
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}

class TornadoExternalInputListSource extends TaintSource {

    TornadoExternalInputListSource() {
        exists(string name |
            name = "get_arguments" or
            name = "get_query_arguments" or
            name = "get_body_arguments"
            |
            this = callToNamedTornadoRequestHandlerMethod(name)
        )
    }

    string toString() {
        result = "Tornado request method"
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof ExternalStringSequenceKind
    }

}

