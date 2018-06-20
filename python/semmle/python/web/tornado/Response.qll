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

import Tornado

class TornadoConnection extends TaintKind {

    TornadoConnection() {
        this = "tornado.http.connection"
    }

}

class TornadoConnectionSource extends TaintSource {

    TornadoConnectionSource() {
        isTornadoRequestHandlerInstance(this.(AttrNode).getObject("connection"))
    }

    string toString() {
        result = "Tornado http connection source"
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof TornadoConnection
    }

}

class TornadoConnectionWrite extends TaintSink {

    string toString() {
        result = "tornado.connection.write"
    }

    TornadoConnectionWrite() {
        exists(CallNode call, ControlFlowNode conn |
            conn = call.getFunction().(AttrNode).getObject("write") and
            this = call.getAnArg() |
            exists(TornadoConnection tc | tc.taints(conn))
            or
            isTornadoRequestHandlerInstance(conn)
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}

class TornadoHttpRequestHandlerWrite extends TaintSink {

    string toString() {
        result = "tornado.HttpRequesHandler.write"
    }

    TornadoHttpRequestHandlerWrite() {
        exists(CallNode call, ControlFlowNode node |
            node = call.getFunction().(AttrNode).getObject("write") and
            isTornadoRequestHandlerInstance(node) and
            this = call.getAnArg()
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}

class TornadoHttpRequestHandlerRedirect extends TaintSink {

    string toString() {
        result = "tornado.HttpRequesHandler.redirect"
    }

    TornadoHttpRequestHandlerRedirect() {
        exists(CallNode call, ControlFlowNode node |
            node = call.getFunction().(AttrNode).getObject("redirect") and
            isTornadoRequestHandlerInstance(node) and
            this = call.getArg(0)
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}



