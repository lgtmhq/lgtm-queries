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

/** Generic taint source from a http request */
abstract class SimpleHttpRequestTaintSource extends TaintSource {

    predicate isSourceOf(TaintKind kind) { 
        kind instanceof ExternalStringKind
    }

}

/** Gets an http verb */
string httpVerb() {
    result = "GET" or result = "POST" or
    result = "PUT" or result = "PATCH" or
    result = "DELETE" or result = "OPTIONS" or
    result = "HEAD"
}

/** Gets an http verb, in lower case */
string httpVerbLower() {
    result = httpVerb().toLowerCase()
}
