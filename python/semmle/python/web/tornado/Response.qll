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
        this.(AttrNode).getObject("connection").refersTo(_, aTornadoRequestHandlerClass(), _)
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
            call.getFunction().(AttrNode).getObject("write") = conn and
            this = call.getAnArg() |
            exists(TornadoConnection tc | tc.taints(conn))
            or
            conn.refersTo(_, aTornadoRequestHandlerClass(), _)
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
        exists(CallNode call, ControlFlowNode req |
            call.getFunction().(AttrNode).getObject("write") = req and
            this = call.getAnArg() and
            req.refersTo(_, aTornadoRequestHandlerClass(), _)
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
        exists(CallNode call, ControlFlowNode req |
            call.getFunction().(AttrNode).getObject("redirect") = req and
            this = call.getArg(0) and
            req.refersTo(_, aTornadoRequestHandlerClass(), _)
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}



