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
import semmle.python.web.flask.General

private Object theFlaskRequestObject() {
    result = theFlaskModule().getAttribute("request")

}

/** Holds if `attr` is an access of attribute `name` of the flask request object */
private predicate flask_request_attr(AttrNode attr, string name) {
    attr.isLoad() and
    attr.getObject(name).refersTo(theFlaskRequestObject())
}

/** Source of external data from a flask request */
class FlaskRequestData extends SimpleHttpRequestTaintSource {

    FlaskRequestData() {
        not this instanceof FlaskRequestArgs and
        exists(string name |
            flask_request_attr(this, name) |
            name = "path" or name = "full_path" or
            name = "base_url" or name = "url"
        )
    }

    string toString() {
        result = "flask.request"
    }

}

/** Source of dictionary whose values are externally controlled */
class FlaskRequestArgs extends TaintSource {

    FlaskRequestArgs() {
        exists(string attr |
            flask_request_attr(this, attr) |
            attr = "args" or attr = "form" or
            attr = "values" or attr = "files" or
            attr = "headers" or attr = "json"
        )
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof ExternalStringDictKind
    }

    string toString() {
        result = "flask.request.args"
    }

}


/** Source of dictionary whose values are externally controlled */
class FlaskRequestJson extends TaintSource {

    FlaskRequestJson() {
        flask_request_attr(this, "json")
    }

    predicate isSourceOf(TaintKind kind) {
        kind instanceof ExternalJsonKind
    }

    string toString() {
        result = "flask.request.json"
    }

}

