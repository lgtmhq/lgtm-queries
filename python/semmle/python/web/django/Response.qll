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
private import semmle.python.web.django.Shared


/** A django.http.response.Response object
 * This isn't really a "taint", but we use the value tracking machinery to
 * track the flow of response objects.
 */
class DjangoResponse extends TaintKind {

    DjangoResponse() {
        this = "django.response.HttpResponse"
    }

}

private ClassObject theDjangoHttpResponseClass() {
    result = any(ModuleObject m | m.getName() = "django.http.response").getAttribute("HttpResponse") and
    not result = theDjangoHttpRedirectClass()
}

/** Instantiation of a django response. */
class DjangoResponseSource extends TaintSource {

    DjangoResponseSource() {
        exists(ClassObject cls |
            cls.getAnImproperSuperType() = theDjangoHttpResponseClass() and
            cls.getACall() = this
        )
    }

    override predicate isSourceOf(TaintKind kind) { kind instanceof DjangoResponse }

    string toString() {
        result = "django.http.response.HttpResponse"
    }
}

/** A write to a django response, which is vulnerable to external data (xss) */
class DjangoResponseWrite extends TaintSink {

    DjangoResponseWrite() {
        exists(AttrNode meth, CallNode call |
            call.getFunction() = meth and
            any(DjangoResponse repsonse).taints(meth.getObject("write")) and
            this = call.getArg(0)
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

    string toString() {
        result = "django.Response.write(...)"
    }

}

/** An argument to initialization of a django response, which is vulnerable to external data (xss) */
class DjangoResponseContent extends TaintSink {

    DjangoResponseContent() {
        exists(CallNode call, ClassObject cls |
            cls.getAnImproperSuperType() = theDjangoHttpResponseClass() and
            call.getFunction().refersTo(cls) |
            call.getArg(0) = this
            or
            call.getArgByName("content") = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

    string toString() {
        result = "django.Response(...)"
    }

}



