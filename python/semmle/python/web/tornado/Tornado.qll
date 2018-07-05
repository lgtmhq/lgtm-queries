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

private ClassObject theTornadoRequestHandlerClass() {
    result = any(ModuleObject m | m.getName() = "tornado.web").getAttribute("RequestHandler")
}

ClassObject aTornadoRequestHandlerClass() {
    result.getASuperType() = theTornadoRequestHandlerClass()
}

FunctionObject getTornadoRequestHandlerMethod(string name) {
    result = theTornadoRequestHandlerClass().declaredAttribute(name)
}

/** Holds if `node` is likely to refer to an instance of a tornado 
 * `RequestHandler` class.
 */

predicate isTornadoRequestHandlerInstance(ControlFlowNode node) {
    node.refersTo(_, aTornadoRequestHandlerClass(), _)
    or
    /* In some cases, the points-to analysis won't capture all instances we care
     * about. For these, we use the following syntactic check. First, that 
     * `node` appears inside a method of a subclass of 
     * `tornado.web.RequestHandler`:*/
    node.getScope().getEnclosingScope().(Class).getClassObject() = aTornadoRequestHandlerClass() and
    /* Secondly, that `node` refers to the `self` argument: */
    node.isLoad() and node.(NameNode).isSelf()
}

CallNode callToNamedTornadoRequestHandlerMethod(string name) {
    isTornadoRequestHandlerInstance(result.getFunction().(AttrNode).getObject(name))
}