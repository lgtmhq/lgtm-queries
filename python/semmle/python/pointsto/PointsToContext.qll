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
private import semmle.python.pointsto.Final
private import semmle.python.pointsto.Penultimate

/*
 * A note on 'cost'. Cost doesn't represent the cost to compute,
 * but (a vague estimate of) the cost to compute per value gained.
 * This is constantly evolving, so see the various cost functions below for more details.
 */

private int given_cost() {
    exists(string depth | 
        py_flags_versioned("context.cost", depth, _) and
        result = depth.toInt()
    )
}

private int max_context_cost() {
    not py_flags_versioned("context.cost", _, _) and result = 7
    or
    result = max(int cost | cost = given_cost() | cost)
}

private int context_cost(TFinalContext ctx) {
    ctx = TMainContext() and result = 0
    or
    ctx = TRuntimeContext() and result = 0
    or
    ctx = TImportContext() and result = 0
    or
    ctx = TCallContext(_, _, result)
}

private int call_cost(CallNode call) {
    if call.getScope().inSource() then
        result = 2
    else
        result = 3
}

private int incoming_calls_estimate(FunctionObject f) {
    result = count(PenultimatePointsTo::get_a_call(f, _))+1
}

/** Cost of contexts for a call, the more callers the 
 * callee of call has the more expensive it is to add contexts for it.
 * This seems to be an effective heuristics for preventing an explosion
 * in the number of contexts while retaining good results.
 */
private int splay_cost(CallNode c) {
    exists(PyFunctionObject func | 
        PenultimatePointsTo::get_a_call(func, _) = c and
        result = incoming_calls_estimate(func).log(2).floor()
    )
    or
    not exists(FunctionObject func | 
        PenultimatePointsTo::get_a_call(func, _) = c
    ) and result = 0
}

private predicate call_to_init_or_del(CallNode call) {
    exists(string mname |
        mname =  "__init__" or mname =  "__del__" |
        mname = call.getFunction().(AttrNode).getName()
    )
}

/** Total cost estimate */
private int total_call_cost(CallNode call) {
    /* We want to always follow __init__ and __del__ calls as they tell us about object construction,
     * but we need to be aware of cycles, so they must have a non-zero cost.
     */
    if call_to_init_or_del(call) then
        result = 1
    else
        result = call_cost(call) + splay_cost(call)
}

private int total_cost(CallNode call, FinalContext outerContext) {
    outerContext.appliesTo(call) and
    result = total_call_cost(call) + context_cost(outerContext)
}

private cached newtype TFinalContext =
    TMainContext()
    or
    TRuntimeContext()
    or
    TImportContext()
    or
    TCallContext(ControlFlowNode call, FinalContext outerContext, int cost) {
        total_cost(call, outerContext) = cost and
        cost <= max_context_cost()
    }

/** Points-to context. Context can be one of:
 *    * "main": Used for scripts.
 *    * "import": Use for non-script modules.
 *    * "default": Use for functions and methods without caller context.
 *    * All other contexts are call contexts and consist of a pair of call-site and caller context.
 */
class FinalContext extends TFinalContext {

    cached string toString() {
        this = TMainContext() and result = "main"
        or
        this = TRuntimeContext() and result = "runtime"
        or
        this = TImportContext() and result = "import"
        or
        exists(CallNode callsite, FinalContext outerContext |
            this = TCallContext(callsite, outerContext, _) and
            result = callsite.getLocation() + " from " + outerContext.toString()
        )
    }

    /** Holds if `call` is the call-site from which this context was entered and `outer` is the caller's context. */
    predicate fromCall(CallNode call, FinalContext caller) {
        caller.appliesTo(call) and
        this = TCallContext(call, caller, _)
    }

    /** Holds if `call` is the call-site from which this context was entered and `outer` is the caller's context. */
    predicate fromCall(CallNode call, FunctionObject callee, FinalContext caller) {
        call = FinalPointsTo::get_a_call(callee, caller) and
        this = TCallContext(call, caller, _)
    }

     /** Gets the caller context for this callee context. */
    FinalContext getOuter() {
        this = TCallContext(_, result, _)
    }

    /** Holds if this context is relevant to the given scope. */
    predicate appliesToScope(Scope s) {
        /* Scripts */
        this = TMainContext() and maybe_main(s)
        or
        /* Modules and classes evaluated at import */
        s instanceof ImportTimeScope and this = TImportContext()
        or
        this = TRuntimeContext() and executes_in_runtime_context(s)
        or
        /* Called functions, regardless of their name */
        exists(FunctionObject func, ControlFlowNode call, TFinalContext outerContext |
            call = FinalPointsTo::get_a_call(func, outerContext) and
            this = TCallContext(call, outerContext, _) and
            s = func.getFunction()
        )
    }

    /** Holds if this context can apply to the CFG node `n`. */
    pragma [inline] 
    predicate appliesTo(ControlFlowNode n) {
        this.appliesToScope(n.getScope())
    }

    /** Holds if this context is a call context. */
    predicate isCall() {
        this = TCallContext(_, _, _)
    }

    /** Holds if this is the "main" context. */
    predicate isMain() {
        this = TMainContext()
    }

    /** Holds if this is the "import" context. */
    predicate isImport() {
        this = TImportContext()
    }

    /** Holds if this is the "default" context. */
    predicate isRuntime() {
        this = TRuntimeContext()
    }

    /** Holds if this context or one of its caller contexts is the default context. */
    predicate fromRuntime() { 
        this.isRuntime()
        or
        this.getOuter().fromRuntime()
    }

    /** INTERNAL -- Do not use */
    predicate isFinal() { any() }

    /** Gets the depth (number of calls) for this context. */
    int getDepth() {
        not exists(this.getOuter()) and result = 0
        or
        result = this.getOuter().getDepth() + 1
    }

    int getCost() {
        result = context_cost(this)
    }

    /** Holds if a call would be too expensive to create a new context for */
    predicate untrackableCall(CallNode call) {
        total_cost(call, this) > max_context_cost()
    }

}

private predicate in_source(Scope s) {
    exists(s.getEnclosingModule().getFile().getRelativePath())
}

/** Holds if this scope can be executed in the default context.
 * All modules and classes executed at import time and
 * all "public" functions and methods, including those invoked by the VM.
 */
predicate executes_in_runtime_context(Function f) {
    /* "Public" scope, i.e. functions whose name starts not with an underscore, or special methods */
    (f.getName().charAt(0) != "_" or f.isSpecialMethod() or f.isInitMethod()) 
    and 
    in_source(f)
}

private predicate maybe_main(Module m) {
    exists(If i, Compare cmp, Name name, StrConst main |
        m.getAStmt() = i and i.getTest() = cmp |
        cmp.compares(name, any(Eq eq), main) and
        name.getId() = "__name__" and
        main.getText() = "__main__"
    )
}


/* Template contexts */

class PreviousContext extends string {

    PreviousContext() { this = "previous" }

}

class ThisContext extends int {
    ThisContext() { this = -1 }

    predicate appliesToScope(Scope s) {
        s instanceof ImportTimeScope
    }

    /** Holds if `call` is the call-site from which this context was entered and `outer` is the caller's context */
    predicate fromCall(CallNode call, ThisContext caller) {
        none()
    }

    /** Holds if `call` is the call-site from which this context was entered and `outer` is the caller's context */
    predicate fromCall(CallNode call, FunctionObject callee, ThisContext caller) {
        none()
    }

    ThisContext getOuter() {
        none()
    }

    predicate appliesTo(ControlFlowNode n) {
        none()
    }

    PreviousContext previous() { none() }

    /** Holds if this the "main" context.
     */
    predicate isMain() { none() }

    /** Holds if this a "call" context.
     */
    predicate isCall() { none() }

    predicate isImport() { none() }

    predicate isRuntime() { none() }

    predicate fromRuntime() { none() }

    predicate isFinal() { any() }

    int getDepth() { result = 0 }

    /** Holds if a call would be too expensive to create a new context for */
    predicate untrackableCall(CallNode call) { none() }

}


/** Contexts for earlier passes */

class Layer0Context extends int {
    Layer0Context() { this = 0 }

    predicate appliesToScope(Scope s) {
        s instanceof ImportTimeScope
    }

    predicate fromCall(CallNode call, Layer0Context caller) {
        none()
    }

    /** Holds if `call` is the call-site from which this context was entered and `outer` is the caller's context */
    predicate fromCall(CallNode call, FunctionObject callee, Layer0Context caller) {
        none()
    }

    Layer0Context getOuter() {
        none()
    }

    pragma [inline] 
    predicate appliesTo(ControlFlowNode n) {
        this.appliesToScope(n.getScope())
    }

    predicate isMain() {
        none()
    }

    predicate isImport() { any() }

    predicate isCall() { none() }

    predicate isRuntime() { any() }

    predicate fromRuntime() { any() }

    predicate isFinal() { none() }

    predicate predecessor(EssaDefinition def, EssaVariable pred_var) {
        none()
    }

    /** Holds if a call would be too expensive to create a new context for */
    predicate untrackableCall(CallNode call) { none() }

}

class PenultimateContext extends int {
    PenultimateContext() { this = 1 }

    predicate appliesToScope(Scope s) {
        any()
    }

    predicate fromCall(CallNode call, PenultimateContext caller) {
        none()
    }

    /** Holds if `call` is the call-site from which this context was entered and `outer` is the caller's context */
    predicate fromCall(CallNode call, FunctionObject callee, PenultimateContext caller) {
        none()
    }

    PenultimateContext getOuter() {
        none()
    }

    pragma [inline] 
    predicate appliesTo(ControlFlowNode n) {
        this.appliesToScope(n.getScope())
    }

    predicate isMain() { none() }

    predicate isCall() { none() }

    predicate isImport() { any() }

    predicate isRuntime() { any() }

    predicate fromRuntime() { any() }

    predicate isFinal() { none() }

    predicate predecessor(EssaDefinition def, PenultimateContext pred_context, EssaVariable pred_var) {
        /* Do we want to add a few cases here?
         * Possibly support class & function decorators?
         */
        none()
    }

    /** Holds if a call would be too expensive to create a new context for */
    predicate untrackableCall(CallNode call) { none() }

}
