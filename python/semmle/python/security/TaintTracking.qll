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

/** A 'kind' of taint. This may be almost anything,
 * but it is typically something like a "user-defined string".
 * Examples include, data from a http request object,
 * data from an SMS or other mobile data source,
 * or, for a super secure system, environment variables or
 * the local file system.
 */
abstract class TaintKind extends string {

    bindingset[this]
    TaintKind() { any() }

    /** Gets the kind of taint that the named attribute will have if an object is tainted with this taint.
     * In other words, if `x` has this kind of taint then it implies that `x.name`
     * has `result` kind of taint.
     */
    TaintKind getTaintOfAttribute(string name) { none() }

    /** Gets the kind of taint results from calling the named method if an object is tainted with this taint.
     * In other words, if `x` has this kind of taint then it implies that `x.name()`
     * has `result` kind of taint.
     */
    TaintKind getTaintOfMethodResult(string name) { none() }

    /** Gets the taint resulting from the addition flow step `fromnode` -> `tonode`. */
    TaintKind getTaintForFlowStep(ControlFlowNode fromnode, ControlFlowNode tonode) { none() }

    /** Holds if this kind of taint passes from variable `fromvar` to  variable `tovar`
     * This predicate is present for completeness. It is unlikely that any `TaintKind`
     * implementation will ever need to override it.
     */
    predicate additionalFlowStepVar(EssaVariable fromvar, EssaVariable tovar) { none() }

    /** Holds if this kind of taint can start from `expr`.
     * In other words, is `expr` a source of this kind of taint.
     */
    final predicate startsFrom(ControlFlowNode expr) {
        expr.(TaintSource).isSourceOf(this, _)
    }

    /** Holds if this kind of taint "taints" `expr`.
     */
    final predicate taints(ControlFlowNode expr) {
        exists(TaintedNode n |
            n.getTaintKind() = this and n.getNode() = expr
        )
    }

}

/** A type of sanitizer of untrusted data.
 * Examples include sanitizers for http responses, for DB access or for shell commands.
 * Usually a sanitizer can only sanitize data for one particular use.
 * For example, a sanitizer for DB commands would not be safe to use for http responses.
 */
abstract class Sanitizer extends string {

    bindingset[this]
    Sanitizer() { any() }

    /** Holds if `taint` cannot flow through `node`. */
    predicate sanitizingNode(TaintKind taint, ControlFlowNode node) { none() }

    /** Holds if `call` removes removes the `taint` */
    predicate sanitizingCall(TaintKind taint, FunctionObject callee) { none() }

    /** Holds if `test` shows value to be untainted with `taint` */
    predicate sanitizingEdge(TaintKind taint, PyEdgeRefinement test) { none() }

    /** Holds if `test` shows value to be untainted with `taint` */
    predicate sanitizingSingleEdge(TaintKind taint, SingleSuccessorGuard test) { none() }

    /** Holds if `def` shows value to be untainted with `taint` */
    predicate sanitizingDefinition(TaintKind taint, EssaDefinition def) { none() }

    /** Holds if the variable is post-sanitized. Uses of this variable will not be
     * sanitized, but the taint will not flow from this variable to other variables 
     * or definitions
     */
    predicate postSanitizedVariable(TaintKind taint, EssaVariable var) { none() }

}

/** A source of taintedness.
 * Users of the taint tracking library should override this
 * class to provide their own sources.
 */
abstract class TaintSource extends @py_flow_node {

    abstract string toString();

    /**
     * Holds if `this` is a source of taint kind `kind`
     *
     * This should be overridden by subclasses to specify sources of taint.
     *
     * The smaller this predicate is, the faster `Taint.flowsTo()` will converge.
     */
    predicate isSourceOf(TaintKind kind) { none() }

    /**
     * Holds if `this` is a source of taint kind `kind` for the given context.
     * Generally, this should not need to be overridden; overriding `isSourceOf(kind)` should be sufficient.
     *
     * The smaller this predicate is, the faster `Taint.flowsTo()` will converge.
     */
    predicate isSourceOf(TaintKind kind, Context context) {
        context.appliesTo(this) and this.isSourceOf(kind)
    }

    Location getLocation() {
        result = this.(ControlFlowNode).getLocation()
    }

    /** Gets a TaintedNode for this taint source */
    TaintedNode getATaintNode() {
        exists(TaintFlow::TrackedTaint taint, Context context |
            this.isSourceOf(taint.getKind(), context) and
            result = TTaintedNode_(taint, context, this)
        )
    }

    /** Holds if taint can flow from this source to sink `sink` */
    final predicate flowsToSink(TaintKind srckind, TaintSink sink) {
        exists(TaintedNode t |
            t = this.getATaintNode() and
            t.getTaintKind() = srckind and
            t.flowsToSink(sink)
        )
    }

    /** Holds if taint can flow from this source to taint sink `sink` */
    final predicate flowsToSink(TaintSink sink) {
        this.flowsToSink(_, sink)
    }

}

abstract class TaintedDefinition extends EssaNodeDefinition {

    /**
     * Holds if `this` is a source of taint kind `kind`
     *
     * This should be overridden by subclasses to specify sources of taint.
     *
     * The smaller this predicate is, the faster `Taint.flowsTo()` will converge.
     */
    predicate isSourceOf(TaintKind kind) { none() }

    /**
     * Holds if `this` is a source of taint kind `kind` for the given context.
     * Generally, this should not need to be overridden; overriding `isSourceOf(kind)` should be sufficient.
     *
     * The smaller this predicate is, the faster `Taint.flowsTo()` will converge.
     */
    predicate isSourceOf(TaintKind kind, Context context) {
        context.appliesToScope(this.getScope()) and this.isSourceOf(kind)
    }

}

/** A node that is vulnerable to one or more types of taint.
 * These nodes provide the sinks when computing the taint flow graph.
 * An example would be an argument to a write to a http response object,
 * such an argument would be vulnerable to unsanitized user-input (XSS).
 *
 * Users of the taint tracking library should extend this
 * class to provide their own sink nodes.
 */
abstract class TaintSink extends  @py_flow_node {

    abstract string toString();

    /**
     * Holds if `this` "sinks" taint kind `kind`
     * Typically this means that `this` is vulnerable to taint kind `kind`.
     *
     * This should be overridden by subclasses to specify vulnerabilities or other sinks of taint.
     */
    abstract predicate sinks(TaintKind taint);

    Location getLocation() {
        result = this.(ControlFlowNode).getLocation()
    }

}

/** Extension for data-flow, to help express data-flow paths that are
 * library or framework specific and cannot be inferred by the general
 * data-flow machinery.
 */
module DataFlowExtension {

    /** A control flow node that modifies the basic data-flow. */
    abstract class DataFlowNode extends @py_flow_node {

        string toString() {
            result = "Dataflow extension node"
        }

        /** Gets a successor node for data-flow.
         * Data (all forms) is assumed to flow from `this` to `result`
         */
        ControlFlowNode getASuccessorNode() { none() }

        /** Gets a successor variable for data-flow.
         * Data (all forms) is assumed to flow from `this` to `result`.
         * Note: This is an unlikely form of flow. See `DataFlowVariable.getASuccessorVariable()`
         */
        EssaVariable getASuccessorVariable() { none() }

        /** Holds if data cannot flow from `this` to `succ`,
         * even though it would normally do so.
         */
        predicate prunedSuccessor(ControlFlowNode succ) { none() }

    }

    /** Data flow variable that modifies the basic data-flow. */
    class DataFlowVariable extends EssaVariable {

        /** Gets a successor node for data-flow.
         * Data (all forms) is assumed to flow from `this` to `result`
         * Note: This is an unlikely form of flow. See `DataFlowNode.getASuccessorNode()`
         */
        ControlFlowNode getASuccessorNode() { none() }

        /** Gets a successor variable for data-flow.
         * Data (all forms) is assumed to flow from `this` to `result`.
         */
        EssaVariable getASuccessorVariable() { none() }

        /** Holds if data cannot flow from `this` to `succ`,
         * even though it would normally do so.
         */
        predicate prunedSuccessor(EssaVariable succ) { none() }

    }

}

private newtype TTaintedNode =
    TTaintedNode_(TaintFlow::TrackedValue taint, Context context, ControlFlowNode n) {
        exists(TaintKind kind |
            taint = TaintFlow::TTrackedTaint(kind) |
            n.(TaintSource).isSourceOf(kind, context)
        )
        or
        TaintFlow::step(_, taint, context, n) and
        exists(TaintKind kind |
            kind = taint.(TaintFlow::TrackedTaint).getKind()
            or
            kind = taint.(TaintFlow::TrackedAttribute).getKind(_) |
            not exists(Sanitizer sanitizer |
                sanitizer.sanitizingNode(kind, n)
            )
        )
        or
        user_tainted_def(_, taint, context, n)
    }

private predicate user_tainted_def(TaintedDefinition def, TaintFlow::TTrackedTaint taint, Context context, ControlFlowNode n) {
    exists(TaintKind kind |
        taint = TaintFlow::TTrackedTaint(kind) and
        def.(TaintedDefinition).isSourceOf(kind, context) and
        n = def.(TaintedDefinition).getDefiningNode()
    )
}

/** A tainted data flow graph node.
 * This is a triple of `(CFG node, data-flow context, taint)`
 */
class TaintedNode extends TTaintedNode {

    string toString() { result = this.getTrackedValue().toString() + " at " + this.getLocation() }

    TaintedNode getASuccessor() {
        exists(TaintFlow::TrackedValue tokind, Context tocontext, ControlFlowNode tonode |
            result = TTaintedNode_(tokind, tocontext, tonode) and
            TaintFlow::step(this, tokind, tocontext, tonode)
        )
    }

    /** Gets the taint for this node. */
    TaintFlow::TrackedValue getTrackedValue() {
      this = TTaintedNode_(result, _, _)
    }

    /** Gets the CFG node for this node. */
    ControlFlowNode getNode() {
        this = TTaintedNode_(_, _, result)
    }

    /** Gets the data-flow context for this node. */
    Context getContext() {
        this = TTaintedNode_(_, result, _)
    }

    Location getLocation() {
        result = this.getNode().getLocation()
    }

    /** Holds if this node is a source of taint */
    predicate isSource() {
        exists(TaintFlow::TrackedTaint taint, Context context, TaintSource node |
            this = TTaintedNode_(taint, context, node) and
            node.isSourceOf(taint.getKind(), context)
        )
    }

    /** Gets the kind of taint that node is tainted with.
     * Doesn't apply if an attribute or item is tainted, only if this node directly tainted
     * */
    TaintKind getTaintKind() {
        this.getTrackedValue().(TaintFlow::TrackedTaint).getKind() = result
    }

    /** Holds if taint flows from this node to the sink `sink` and
     * reaches with a taint that `sink` is a sink of.
     */
    predicate flowsToSink(TaintSink sink) {
        exists(TaintedNode node |
            this.getASuccessor*() = node and
            node.getNode() = sink and
            sink.sinks(node.getTaintKind())
        )
    }

    /** Holds if the underlying CFG node for this node is a vulnerable node
     * and is vulnerable to this node's taint.
     */
    predicate isVulnerableSink() {
        exists(TaintedNode src, TaintSink vuln |
            src.isSource() and
            src.getASuccessor*() = this and
            vuln = this.getNode() and
            vuln.sinks(this.getTaintKind())
        )
    }

}

/** This module contains the implementation of taint-flow.
 * It is recommended that users use the `TaintedNode` class, rather than using this module directly
 * as the interface of this module may change without warning.
 */
module TaintFlow {

    import semmle.python.pointsto.Final
    import DataFlowExtension

    newtype TTrackedValue =
        TTrackedTaint(TaintKind kind)
        or
        TTrackedAttribute(string name, TaintKind kind) {
            exists(AttributeAssignment def, TaintedNode origin |
                def.getName() = name and
                def.getValue() = origin.getNode() and
                origin.getTaintKind() = kind
            )
            or
            exists(ImportExprNode imp, TaintedNode origin, ModuleObject mod |
                imp.refersTo(mod) and
                TaintFlow::module_attribute_tainted(mod, name, origin) and
                origin.getTaintKind() = kind
            )
            or
            exists(TaintKind src |
                kind = src.getTaintOfAttribute(name)
            )
            or
            exists(TaintedNode origin, AttrNode lhs, ControlFlowNode rhs |
                lhs.getName() = name and rhs = lhs.(DefinitionNode).getValue() |
                origin.getNode() = rhs and
                kind = origin.getTaintKind()
            )
        }

    /** The "taint" tracked internal by the TaintFlow module.
     *  This is not the taint kind specified by the user, but describes both the kind of taint
     *  and how that taint relates to any object referred to by a data-flow graph node or edge.
     */
    class TrackedValue extends TTrackedValue {

        abstract string toString();


        TrackedValue toAttribute(string name) {
            this = result.fromAttribute(name)
        }

        abstract TrackedValue fromAttribute(string name);

        abstract TrackedValue toKind(TaintKind kind);

    }

    class TrackedTaint extends TrackedValue, TTrackedTaint {

        string toString() {
            result = "Taint " + this.getKind()
        }

        TaintKind getKind() {
            this = TTrackedTaint(result)
        }

        TrackedValue fromAttribute(string name) {
            none()
        }

        override TrackedValue toKind(TaintKind kind) {
            result = TTrackedTaint(kind)
        }

    }

    class TrackedAttribute extends TrackedValue, TTrackedAttribute {

        string toString() {
            exists(string name, TaintKind kind |
                this = TTrackedAttribute(name, kind) and
                result = "Attribute '" + name + "' taint " + kind
            )
        }

        TaintKind getKind(string name) {
            this = TTrackedAttribute(name, result)
        }

        TrackedValue fromAttribute(string name) {
            exists(TaintKind kind |
                this = TTrackedAttribute(name, kind) and
                result = TTrackedTaint(kind)
            )
        }

        string getName() {
            this = TTrackedAttribute(result, _)
        }

        override TrackedValue toKind(TaintKind kind) {
            result = TTrackedAttribute(this.getName(), kind)
        }

    }

    predicate step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, ControlFlowNode tonode) {
        unpruned_step(fromnode, totaint, tocontext, tonode) and
        tonode.getBasicBlock().likelyReachable()
    }

    predicate unpruned_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, ControlFlowNode tonode) {
        import_step(fromnode, totaint, tocontext, tonode)
        or
        from_import_step(fromnode, totaint, tocontext, tonode)
        or
        attribute_load_step(fromnode, totaint, tocontext, tonode)
        or
        attribute_store_step(fromnode, totaint, tocontext, tonode, _)
        or
        getattr_step(fromnode, totaint, tocontext, tonode)
        or
        use_step(fromnode, totaint, tocontext, tonode)
        or
        call_taint_step(fromnode, totaint, tocontext, tonode)
        or
        fromnode.getNode().(DataFlowNode).getASuccessorNode() = tonode and
        fromnode.getContext() = tocontext and
        totaint = fromnode.getTrackedValue()
        or
        exists(TaintKind tokind |
            tokind = fromnode.getTaintKind().getTaintForFlowStep(fromnode.getNode(), tonode) and
            totaint = fromnode.getTrackedValue().toKind(tokind) and
            tocontext = fromnode.getContext()
        )
        or
        data_flow_step(fromnode.getContext(), fromnode.getNode(), tocontext, tonode) and
        totaint = fromnode.getTrackedValue()
        or
        exists(DataFlowVariable var |
            var.getASuccessorNode() = tonode and
            tainted_var(var, tocontext, fromnode) and
            totaint = fromnode.getTrackedValue()
        )
    }

    predicate import_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, ImportExprNode tonode) {
        tocontext.appliesTo(tonode) and
        exists(ModuleObject mod, string name |
            tonode.refersTo(mod) and
            module_attribute_tainted(mod, name, fromnode) and
            totaint = fromnode.getTrackedValue().toAttribute(name)
        )
    }

    predicate data_flow_step(Context fromcontext, ControlFlowNode fromnode, Context tocontext, ControlFlowNode tonode) {
        if_exp_step(fromcontext, fromnode, tocontext, tonode)
        or
        call_flow_step(fromcontext, fromnode, tocontext, tonode)
        or
        parameter_step(fromcontext, fromnode, tocontext, tonode)
    }

    predicate from_import_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, ControlFlowNode tonode) {
        exists(string name, ImportExprNode fmod, ModuleObject mod |
            fmod = tonode.(ImportMemberNode).getModule(name) and
            fmod.refersTo(mod) and
            tocontext.appliesTo(tonode) and
            module_attribute_tainted(mod, name, fromnode) and
            totaint = fromnode.getTrackedValue()
        )
    }

    predicate getattr_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, CallNode tonode) {
        exists(ControlFlowNode arg, string name |
            tonode.getFunction().refersTo(builtin_object("getattr")) and
            arg = tonode.getArg(0) and
            name = tonode.getArg(1).getNode().(StrConst).getText() and
            arg = fromnode.getNode() and
            totaint = fromnode.getTrackedValue().fromAttribute(name) and
            tocontext = fromnode.getContext()
        )
    }

    predicate attribute_load_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, AttrNode tonode) {
        tonode.isLoad() and
        exists(string name, ControlFlowNode f |
            f = tonode.getObject(name) and
            tocontext = fromnode.getContext() and
            f = fromnode.getNode() and
            (
                totaint = TTrackedTaint(fromnode.getTaintKind().getTaintOfAttribute(name))
                or
                totaint = fromnode.getTrackedValue().fromAttribute(name)
            )
        )
    }

    predicate attribute_store_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, ControlFlowNode tonode, string name) {
        exists(AttrNode lhs, ControlFlowNode rhs |
            tonode = lhs.getObject(name) and rhs = lhs.(DefinitionNode).getValue() |
            fromnode.getNode() = rhs and
            totaint = fromnode.getTrackedValue().toAttribute(name) and
            tocontext = fromnode.getContext()
        )
    }

    predicate module_attribute_tainted(ModuleObject m, string name, TaintedNode origin) {
        exists(EssaVariable var, Context c |
            var.getName() = name and
            var.reachesExit() and
            var.getScope() = m.getModule() and
            tainted_var(var, c, origin) and
            c.isImport()
        )
    }

    predicate use_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, ControlFlowNode tonode) {
        exists(EssaVariable var |
            var.getASourceUse() = tonode and
            unsanitized_tainted_var(var, tocontext, fromnode) and
            totaint = fromnode.getTrackedValue()
        )
    }


    predicate call_flow_step(Context callee, ControlFlowNode fromnode, Context caller, ControlFlowNode call) {
        exists(PyFunctionObject func |
            callee.fromCall(call, func, caller) and
            func.getAReturnedNode() = fromnode
        )
    }

    predicate call_taint_step(TaintedNode fromnode, TrackedValue totaint, Context tocontext, CallNode call) {
        exists(string name |
            call.getFunction().(AttrNode).getObject(name) = fromnode.getNode() and
            totaint = TTrackedTaint(fromnode.getTaintKind().getTaintOfMethodResult(name)) and
            tocontext = fromnode.getContext()
        )
        or
        exists(EssaVariable self, Context callee |
            self_init_end_transfer(self, callee, call, tocontext) and
            tainted_var(self, callee, fromnode) and
            totaint = fromnode.getTrackedValue()
        )
    }

    predicate self_init_end_transfer(EssaVariable self, Context callee, CallNode call, Context caller) {
        exists(ClassObject cls, Function init |
            FinalPointsTo::instantiation(call, caller, cls) and
            init = cls.lookupAttribute("__init__").(FunctionObject).getFunction() and
            self.getSourceVariable().(Variable).isSelf() and self.getScope() = init and
            callee.fromCall(call, caller)
        )
    }

    predicate tainted_var(EssaVariable var, Context context, TaintedNode origin) {
        unsanitized_tainted_var(var, context, origin) and
        (
            origin.getTrackedValue() instanceof TrackedAttribute
            or
            exists(TaintKind kind |
                kind = origin.getTaintKind() and
                not exists(Sanitizer san | san.postSanitizedVariable(kind, var))
            )
        )
    }

    predicate unsanitized_tainted_var(EssaVariable var, Context context, TaintedNode origin) {
        tainted_def(var.getDefinition(), context, origin)
        or
        exists(EssaVariable prev |
            tainted_var(prev, context, origin) and
            prev.(DataFlowVariable).getASuccessorVariable() = var
        )
        or
        origin.getNode().(DataFlowNode).getASuccessorVariable() = var and
        context = origin.getContext()
        or
        exists(TrackedTaint taint, EssaVariable prev |
            tainted_var(prev, context, origin) and
            origin.getTrackedValue() = taint and
            taint.getKind().additionalFlowStepVar(prev, var)
        )
    }

    predicate tainted_def(EssaDefinition def, Context context, TaintedNode origin) {
        unsanitized_tainted_def(def, context, origin) and
        (
            origin.getTrackedValue() instanceof TrackedAttribute
            or
            exists(TaintKind kind |
                kind = origin.getTaintKind() and
                not exists(Sanitizer san | san.sanitizingDefinition(kind, def))
            )
        )
    }

    predicate unsanitized_tainted_def(EssaDefinition def, Context context, TaintedNode origin) {
        exists(TrackedValue val, ControlFlowNode node |
            user_tainted_def(def, val, context, node) and
            origin = TTaintedNode_(val, context, node)
        )
        or
        tainted_phi(def, context, origin)
        or
        tainted_assignment(def, context, origin)
        or
        tainted_attribute_assignment(def, context, origin)
        or
        tainted_parameter_def(def, context, origin)
        or
        tainted_callsite(def, context, origin)
        or
        tainted_method_callsite(def, context, origin)
        or
        tainted_edge(def, context, origin)
        or
        tainted_argument(def, context, origin)
        or
        tainted_import_star(def, context, origin)
        or
        tainted_uni_edge(def, context, origin)
        or
        tainted_scope_entry(def, context, origin)
    }

    predicate tainted_scope_entry(ScopeEntryDefinition def, Context context, TaintedNode origin) {
        /* Transfer from outer scope */
        exists(EssaVariable var, Context outer |
            FinalPointsTo::Flow::scope_entry_value_transfer(var, outer, def, context) and
            tainted_var(var, outer, origin)
        )
    }

    predicate tainted_phi(PhiFunction phi, Context context, TaintedNode origin) {
        exists(BasicBlock pred, EssaVariable predvar |
            predvar = phi.getInput(pred) and
            tainted_var(predvar, context, origin) and
            not pred.unlikelySuccessor(phi.getBasicBlock()) and
            not predvar.(DataFlowExtension::DataFlowVariable).prunedSuccessor(phi.getVariable())
        )
    }

    predicate tainted_assignment(AssignmentDefinition def, Context context, TaintedNode origin) {
        origin.getNode() = def.getValue() and
        context = origin.getContext()
    }

    predicate tainted_attribute_assignment(AttributeAssignment def, Context context, TaintedNode origin) {
        context = origin.getContext() and
        origin.getNode() = def.getDefiningNode().(AttrNode).getObject()
    }

    predicate tainted_callsite(CallsiteRefinement call, Context context, TaintedNode origin) {
        exists(EssaVariable var, Context callee |
            FinalPointsTo::Flow::callsite_exit_value_transfer(var, callee, call, context) and
            tainted_var(var, callee, origin)
        )
    }

    predicate parameter_step(Context caller, ControlFlowNode argument, Context callee, NameNode param) {
        exists(ParameterDefinition def |
            def.getDefiningNode() = param and
            FinalPointsTo::Flow::callsite_transfer(argument, caller, def, callee)
        )
    }

    predicate tainted_parameter_def(ParameterDefinition def, Context context, TaintedNode fromnode) {
        fromnode.getNode() = def.getDefiningNode() and
        context = fromnode.getContext()
    }

    predicate if_exp_step(Context fromcontext, ControlFlowNode operand, Context tocontext, IfExprNode ifexp) {
        fromcontext = tocontext and fromcontext.appliesTo(operand) and
        ifexp.getAnOperand() = operand
    }

    predicate tainted_method_callsite(MethodCallsiteRefinement call, Context context, TaintedNode origin) {
        tainted_var(call.getInput(), context, origin) and
        exists(TaintKind kind |
            kind = origin.getTaintKind() |
            not exists(FunctionObject callee, Sanitizer sanitizer |
                callee.getACall() = call.getCall() and
                sanitizer.sanitizingCall(kind, callee)
            )
        )
    }

    predicate tainted_edge(PyEdgeRefinement test, Context context, TaintedNode origin) {
        exists(EssaVariable var, TaintKind kind |
            kind = origin.getTaintKind() and
            var = test.getInput() and
            tainted_var(var, context, origin) and
            not exists(Sanitizer sanitizer |
                sanitizer.sanitizingEdge(kind, test)
            )
        )
    }

    predicate tainted_argument(ArgumentRefinement def, Context context, TaintedNode origin) {
        tainted_var(def.getInput(), context, origin)
    }

    predicate tainted_import_star(ImportStarRefinement def, Context context, TaintedNode origin) {
        exists(ModuleObject mod, string name |
            FinalPointsTo::Flow::module_and_name_for_import_star(mod, name, def, context) |
            /* Attribute from imported module */
            mod.exports(name) and
            module_attribute_tainted(mod, name, origin) and
            context.appliesTo(def.getDefiningNode())
            or
            exists(EssaVariable var |
                /* Retain value held before import */
                var = def.getInput() and
                FinalPointsTo::Flow::variable_not_redefined_by_import_star(var, context, def) and
                tainted_var(var, context, origin)
            )
        )
    }

    predicate tainted_uni_edge(SingleSuccessorGuard uniphi, Context context, TaintedNode origin) {
        exists(EssaVariable var, TaintKind kind |
            kind = origin.getTaintKind() and
            var = uniphi.getInput() and
            tainted_var(var, context, origin) and
            not exists(Sanitizer sanitizer |
                sanitizer.sanitizingSingleEdge(kind, uniphi)
            )
        )
    }

}

