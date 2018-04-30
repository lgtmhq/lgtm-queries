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
 * may represent malicious OS commands.
 *
 * This module is intended to be imported into a traint-tracking query
 * to extend `TaintKind` and `TaintSink`.
 *
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Untrusted


private ModuleObject subprocessModule() {
    result.getName() = "subprocess"
}

private ModuleObject osModule() {
    result.getName() = "os"
}

private Object makeOsCall() {
    exists(string name |
        result = subprocessModule().getAttribute(name) |
        name = "Popen" or
        name = "call" or 
        name = "check_call" or
        name = "check_output"
    )
}

/**Special case for first element in sequence. */
class FirstElementKind extends TaintKind {

    FirstElementKind() {
        this = "sequence[" + any(ExternalStringKind key) + "][0]"
    }


    /** Gets the taint kind for item in this sequence. */
    ExternalStringKind getItem() {
        this = "sequence[" + result + "][0]"
    }

}

class FirstElementFlow extends DataFlowExtension::DataFlowNode {

    FirstElementFlow() {
        this = any(SequenceNode s).getElement(0)
    }

    override
    ControlFlowNode getASuccessorNode(TaintKind fromkind, TaintKind tokind) {
        result.(SequenceNode).getElement(0) = this and tokind.(FirstElementKind).getItem() = fromkind
    }

}

/** A taint sink that is potentially vulnerable to malicious shell commands.
 *  The `vuln` in `subprocess.call(shell=vuln)` and similar calls.
 */
class ShellCommand extends TaintSink {

    string toString() { result = "shell command" }

    ShellCommand() {
        exists(CallNode call, Object istrue |
            call.getFunction().refersTo(makeOsCall()) and
            call.getAnArg() = this and
            call.getArgByName("shell").refersTo(istrue) and
            istrue.booleanValue() = true
        )
        or
        exists(CallNode call |
            call.getFunction().refersTo(osModule().getAttribute("system")) and
            call.getAnArg() = this
        )
    }

    predicate sinks(TaintKind kind) {
        /* Tainted string command */
        kind instanceof ExternalStringKind
        or
        /* List (or tuple) containing a tainted string command */
        kind instanceof ExternalStringSequenceKind
    }

}

/** A taint sink that is potentially vulnerable to malicious shell commands.
 *  The `vuln` in `subprocess.call(vuln, ...)` and similar calls.
 */
class OsCommandFirstArgument extends TaintSink {

    string toString() { result = "OS command first argument" }

    OsCommandFirstArgument() {
        not this instanceof ShellCommand and
        exists(CallNode call|
            call.getFunction().refersTo(makeOsCall()) and
            call.getArg(0) = this
        )
    }

    predicate sinks(TaintKind kind) {
        /* Tainted string command */
        kind instanceof ExternalStringKind
        or
        /* List (or tuple) whose first element is tainted */
        kind instanceof FirstElementKind
    }

}
