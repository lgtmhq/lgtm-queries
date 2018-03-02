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
import semmle.python.web.Http

/** The flask app class */
ClassObject flaskClass() {
    exists(ModuleObject flask |
        flask.getName() = "flask" and
        result = flask.getAttribute("Flask")
    )
}

/** The flask MethodView class */
ClassObject theMethodViewClass() {
    exists(ModuleObject views |
        views.getName() = "flask.views" and
        result = views.getAttribute("MethodView")
    )
}

ClassObject theReponseClass() {
    exists(ModuleObject flask |
        flask.getName() = "flask" and
        result = flask.getAttribute("Response")
    )
}

/** Holds if `route` is routed to `func`
 * by decorating `func` with `app.route(route)`
 */
predicate app_route(ControlFlowNode route, Function func) {
    exists(CallNode route_call, CallNode decorator_call |
        route_call.getFunction().(AttrNode).getObject("route").refersTo(_, flaskClass(), _) and
        decorator_call.getFunction() = route_call and
        route_call.getArg(0) = route and
        decorator_call.getArg(0).getNode().(FunctionExpr).getInnerScope() = func
    )
}

/* Helper for add_url_rule */
private predicate add_url_rule_call(ControlFlowNode regex, ControlFlowNode callable) {
    exists(CallNode call |
        call.getFunction().(AttrNode).getObject("add_url_rule").refersTo(_, flaskClass(), _) and
        regex = call.getArg(0) |
        callable = call.getArg(2) or
        callable = call.getArgByName("view_func")
    )
}

/** Holds if urls matching `regex` are routed to `func` */
predicate add_url_rule(ControlFlowNode regex, Function func) {
    exists(ControlFlowNode callable |
        add_url_rule_call(regex, callable)
        |
        exists(PyFunctionObject f | f.getFunction() = func and callable.refersTo(f))
        or
        /* MethodView.as_view() */
        exists(MethodViewClass view_cls |
            view_cls.asTaint().taints(callable) |
            func = view_cls.lookupAttribute(httpVerbLower()).(FunctionObject).getFunction()
        )
        /* TO DO -- Handle Views that aren't MethodViews */
    )
}

/** Holds if urls matching `regex` are routed to `func` using 
 * any of flask's routing mechanisms.
 */
predicate flask_routing(ControlFlowNode regex, Function func) {
    app_route(regex, func)
    or
    add_url_rule(regex, func)
}

/** A class that extends flask.views.MethodView */
private class MethodViewClass extends ClassObject {

    MethodViewClass() {
        this.getAnImproperSuperType() = theMethodViewClass()
    }

    /* As we are restricted to strings for taint kinds, we need to map these classes to strings. */
    string taintString() {
        result = "flask/" + this.getQualifiedName() +  ".as.view"
    }

    /* As we are restricted to strings for taint kinds, we need to map these classes to strings. */
    TaintKind asTaint() {
        result = this.taintString()
    }
}

private class MethodViewTaint extends TaintKind {

    MethodViewTaint() {
        any(MethodViewClass cls).taintString() = this
    }
}

/** A source of method view "taint"s. */
private class AsView extends TaintSource {

    AsView() {
        exists(ClassObject view_class |
            view_class.getAnImproperSuperType() = theMethodViewClass() and
            this.(CallNode).getFunction().(AttrNode).getObject("as_view").refersTo(view_class)
        )
    }

    string toString() {
        result = "flask.MethodView.as_view()"
    }

    override predicate isSourceOf(TaintKind kind) {
        exists(MethodViewClass view_class |
            kind = view_class.asTaint() and
            this.(CallNode).getFunction().(AttrNode).getObject("as_view").refersTo(view_class)
        )
    }

}

