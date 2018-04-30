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

/** Provides class and predicates to track external data that
 * may represent malicious yaml-encoded objects.
 *
 * This module is intended to be imported into a traint-tracking query
 * to extend `TaintKind` and `TaintSink`.
 *
 */

import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Untrusted


private ModuleObject yamlModule() {
    result.getName() = "yaml"
}


private FunctionObject yamlLoad() {
    result = yamlModule().getAttribute("load")
}

/** `yaml.load(untrusted)` vulnerability. */
class YamlLoadNode extends TaintSink {

    string toString() { result = "yaml.load vulnerability" }

    YamlLoadNode() {
        exists(CallNode call |
            yamlLoad().getACall() = call and
            call.getAnArg() = this
        )
    }

    predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}
