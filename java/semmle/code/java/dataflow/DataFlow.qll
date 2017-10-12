// Copyright 2017 Semmle Ltd.
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

/**
 * Provides classes for performing local (intra-procedural) and
 * global (inter-procedural) data flow analyses.
 */

import java
private import SSA
private import DefUse
private import semmle.code.java.dispatch.VirtualDispatch

module DataFlow {

  private newtype TNode =
    TExprNode(Expr e) or
    TParameterNode(Parameter p) { exists(p.getCallable().getBody()) } or
    TImplicitVarargsArray(Call c) { c.getCallee().isVarargs() and not exists(Argument arg | arg.getCall() = c and arg.isExplicitVarargsArray()) }

  /**
   * An element, viewed as a node in a data flow graph. Either an expression,
   * a parameter, or an implicit varargs array creation.
   */
  class Node extends TNode {
    /** Gets a textual representation of this element. */
    string toString() { none() }

    /** The source location for this element. */
    Location getLocation() { none() }

    /** Gets the expression corresponding to this node, if any. */
    Expr asExpr() { result = this.(ExprNode).getExpr() }

    /** Gets the parameter corresponding to this node, if any. */
    Parameter asParameter() { result = this.(ParameterNode).getParameter() }

    /** Gets the type of this node. */
    Type getType() {
      result = this.asExpr().getType() or
      result = this.asParameter().getType() or
      exists(Parameter p | result = p.getType() and p.isVarargs() and p = this.(ImplicitVarargsArray).getCall().getCallee().getAParameter())
    }

    /** Gets the callable in which this node occurs. */
    Callable getEnclosingCallable() {
      result = this.asExpr().getEnclosingCallable() or
      result = this.asParameter().getCallable() or
      result = this.(ImplicitVarargsArray).getCall().getEnclosingCallable()
    }
  }

  /**
   * An expression, viewed as a node in a data flow graph.
   */
  class ExprNode extends Node, TExprNode {
    Expr expr;
    ExprNode() { this = TExprNode(expr) }
    override string toString() { result = expr.toString() }
    override Location getLocation() { result = expr.getLocation() }
    /** Gets the expression corresponding to this node. */
    Expr getExpr() { result = expr }
  }

  /** Gets the node corresponding to `e`. */
  ExprNode exprNode(Expr e) { result.getExpr() = e }

  /**
   * A parameter, viewed as a node in a data flow graph.
   */
  class ParameterNode extends Node, TParameterNode {
    Parameter param;
    ParameterNode() { this = TParameterNode(param) }
    override string toString() { result = param.toString() }
    override Location getLocation() { result = param.getLocation() }
    /** Gets the parameter corresponding to this node. */
    Parameter getParameter() { result = param }
  }

  /** Gets the node corresponding to `p`. */
  ParameterNode parameterNode(Parameter p) { result.getParameter() = p }

  /**
   * An implicit varargs array creation expression.
   *
   * A call `f(x1, x2)` to a method `f(A... xs)` desugars to `f(new A[]{x1, x2})`,
   * and this node corresponds to such an implicit array creation.
   */
  class ImplicitVarargsArray extends Node, TImplicitVarargsArray {
    Call call;
    ImplicitVarargsArray() { this = TImplicitVarargsArray(call) }
    override string toString() { result = "new ..[] { .. }" }
    override Location getLocation() { result = call.getLocation() }
    /** Gets the call containing this varargs array creation argument. */
    Call getCall() { result = call }
  }

  /**
   * A data flow node that occurs as the argument of a call and is passed as-is
   * to the callable. Arguments that are wrapped in an implicit varargs array
   * creation are not included, but the implicitly created array is.
   */
  private class ArgumentNode extends Node {
    ArgumentNode() {
      exists(Argument arg | this.asExpr() = arg | not arg.isVararg()) or
      this instanceof ImplicitVarargsArray
    }

    /** Holds if this argument occurs at the given position in the given call. */
    predicate argumentOf(Call call, int pos) {
      exists(Argument arg | this.asExpr() = arg | call = arg.getCall() and pos = arg.getPosition()) or
      call = this.(ImplicitVarargsArray).getCall() and pos = call.getCallee().getNumberOfParameters() - 1
    }
  }

  /** A data flow node that occurs as the result of a `ReturnStmt`. */
  private class ReturnNode extends ExprNode {
    ReturnNode() {
      exists(ReturnStmt ret | this.getExpr() = ret.getResult())
    }
    override Callable getEnclosingCallable() { result = super.getEnclosingCallable() }
  }

  /**
   * A global (inter-procedural) data flow configuration.
   *
   * Each use of the global data flow library must define its own unique extension
   * of this abstract class. A configuration defines a set of relevant sources
   * (`isSource`) and sinks (`isSink`), and may additionally prohibit intermediate
   * flow nodes (`isBarrier`) as well as add custom local data flow steps
   * (`isAdditionalFlowStep()`).
   */
  abstract class Configuration extends string {
    bindingset[this]
    Configuration() { any() }

    /**
     * Holds if `source` is a relevant data flow source.
     */
    abstract predicate isSource(Node source);

    /**
     * Holds if `sink` is a relevant data flow sink.
     */
    abstract predicate isSink(Node sink);

    /** Holds if the intermediate data flow node `node` is prohibited. */
    predicate isBarrier(Node node) { none() }

    /**
     * Holds if the additional flow step from `node1` to `node2` must be taken
     * into account in the analysis.
     *
     * `node1` and `node2` should belong to the same `Callable`.
     */
    predicate isAdditionalFlowStep(Node node1, Node node2) { none() }

    /**
     * Holds if data may flow from `source` to `sink` for this configuration.
     */
    predicate hasFlow(Node source, Node sink) {
      flowsTo(source, sink, this)
    }
  }

  /**
   * Holds if data can flow from `node1` to `node2` in zero or more
   * local (intra-procedural) steps.
   */
  predicate localFlow(Node node1, Node node2) {
    localFlowStep*(node1, node2)
  }

  /**
   * Holds if data can flow from `node1` to `node2` in one local step.
   */
  predicate localFlowStep(Node node1, Node node2) {
    // Variable flow steps through adjacent def-use and use-use pairs.
    exists(SsaExplicitUpdate upd |
      upd.getDefiningExpr().(VariableAssign).getSource() = node1.asExpr() or
      upd.getDefiningExpr().(AssignOp) = node1.asExpr()
      |
      node2.asExpr() = upd.getAFirstUse()
    ) or
    exists(SsaImplicitInit init |
      init.isParameterDefinition(node1.asParameter()) and
      node2.asExpr() = init.getAFirstUse()
    ) or
    adjacentUseUse(node1.asExpr(), node2.asExpr()) or
    node2.asExpr().(ParExpr).getExpr() = node1.asExpr() or
    node2.asExpr().(CastExpr).getExpr() = node1.asExpr() or
    node2.asExpr().(ConditionalExpr).getTrueExpr() = node1.asExpr() or
    node2.asExpr().(ConditionalExpr).getFalseExpr() = node1.asExpr() or
    node2.asExpr().(AssignExpr).getSource() = node1.asExpr()
  }

  /**
   * Holds if data can flow in one local step from `node1` to `node2` taking
   * additional steps from the configuration into account.
   */
  bindingset[config]
  private predicate localFlowStep(Node node1, Node node2, Configuration config) {
    localFlowStep(node1, node2) or
    config.isAdditionalFlowStep(node1, node2)
  }

  /**
   * Holds if the `FieldRead` is not completely determined by explicit SSA
   * updates.
   */
  private predicate hasNonlocalValue(FieldRead fr) {
    not exists(SsaVariable v | v.getAUse() = fr) or
    exists(SsaVariable v, SsaVariable def |
      v.getAUse() = fr and def = v.getAnUltimateDefinition()
      |
      def instanceof SsaImplicitInit or
      def instanceof SsaImplicitUpdate
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a static field.
   */
  private predicate staticFieldStep(ExprNode node1, ExprNode node2) {
    exists(Field f, FieldRead fr |
      f.isStatic() and
      f.getAnAssignedValue() = node1.getExpr() and
      fr.getField() = f and
      fr = node2.getExpr() and
      hasNonlocalValue(fr)
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` through variable capture.
   */
  private predicate variableCaptureStep(Node node1, ExprNode node2) {
    exists(SsaImplicitInit closure, SsaVariable captured |
      closure.captures(captured) and
      node2.getExpr() = closure.getAFirstUse()
      |
      node1.asExpr() = captured.getAUse() or
      not exists(captured.getAUse()) and
      exists(SsaVariable capturedDef | capturedDef = captured.getAnUltimateDefinition() |
        capturedDef.(SsaImplicitInit).isParameterDefinition(node1.asParameter()) or
        capturedDef.(SsaExplicitUpdate).getDefiningExpr().(VariableAssign).getSource() = node1.asExpr() or
        capturedDef.(SsaExplicitUpdate).getDefiningExpr().(AssignOp) = node1.asExpr()
      )
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a static field or
   * variable capture.
   */
  private predicate jumpStep(Node node1, Node node2) {
    staticFieldStep(node1, node2) or
    variableCaptureStep(node1, node2)
  }

  /**
   * Holds if `p` is the `i`th parameter of a viable dispatch target of `call`.
   */
  pragma[nomagic]
  private predicate viableParam(Call call, int i, ParameterNode p) {
    exists(Callable callable |
      callable = viableCallable(call) and
      callable.getParameter(i) = p.getParameter()
    )
  }

  /**
   * Holds if `arg` is a possible argument to `p` taking virtual dispatch into account.
   */
  private predicate viableParamArg(ParameterNode p, ArgumentNode arg) {
    exists(int i, Call call |
      viableParam(call, i, p) and
      arg.argumentOf(call, i)
    )
  }

  /**
   * Holds if `node` is reachable from a source in the given configuration
   * ignoring call contexts.
   */
  private predicate nodeCandFwd(Node node, Configuration config) {
    not config.isBarrier(node) and
    (
      config.isSource(node)
      or
      exists(Node mid |
        nodeCandFwd(mid, config) and
        localFlowStep(mid, node, config)
      )
      or
      exists(Node mid |
        nodeCandFwd(mid, config) and
        jumpStep(mid, node)
      )
      or
      // flow into a callable
      exists(Node arg |
        nodeCandFwd(arg, config) and
        viableParamArg(node, arg)
      )
      or
      // flow out of a callable
      exists(Method m, MethodAccess ma, ReturnNode ret |
        nodeCandFwd(ret, config) and
        m = ret.getEnclosingCallable() and
        m = viableImpl(ma) and
        node.asExpr() = ma
      )
    )
  }

  /**
   * Holds if `node` is part of a path from a source to a sink in the given
   * configuration ignoring call contexts.
   */
  private predicate nodeCand(Node node, Configuration config) {
    nodeCandFwd(node, config) and
    (
      config.isSink(node)
      or
      exists(Node mid |
        localFlowStep(node, mid, config) and
        nodeCand(mid, config)
      )
      or
      exists(Node mid |
        jumpStep(node, mid) and
        nodeCand(mid, config)
      )
      or
      // flow into a callable
      exists(Node param |
        viableParamArg(param, node) and
        nodeCand(param, config)
      )
      or
      // flow out of a callable
      exists(Method m, ExprNode ma |
        nodeCand(ma, config) and
        m = node.(ReturnNode).getEnclosingCallable() and
        m = viableImpl(ma.getExpr())
      )
    )
  }

  /**
   * Holds if `node` can be the first node in a maximal subsequence of local
   * flow steps in a dataflow path.
   */
  private predicate localFlowEntry(Node node, Configuration config) {
    nodeCand(node, config) and
    (
      config.isSource(node) or
      jumpStep(_, node) or
      node instanceof ParameterNode or
      node.asExpr() instanceof MethodAccess
    )
  }

  /**
   * Holds if `node` can be the last node in a maximal subsequence of local
   * flow steps in a dataflow path.
   */
  private predicate localFlowExit(Node node, Configuration config) {
    nodeCand(node, config) and
    (
      jumpStep(node, _) or
      node instanceof ArgumentNode or
      node instanceof ReturnNode
    )
  }

  /**
   * Holds if the local path from `node1` to `node2` is a prefix of a maximal
   * subsequence of local flow steps in a dataflow path.
   *
   * This is the transitive closure of `localFlowStep` beginning at `localFlowEntry`.
   */
  private predicate localFlowStepPlus(Node node1, Node node2, Configuration config) {
    localFlowEntry(node1, config) and
    localFlowStep(node1, node2, config) and
    nodeCand(node2, config)
    or
    exists(Node mid |
      localFlowStepPlus(node1, mid, config) and
      localFlowStep(mid, node2, config) and
      nodeCand(node2, config)
    )
  }

  /**
   * Holds if `node1` can step to `node2` in one or more local steps and this
   * path can occur as a maximal subsequence of local steps in a dataflow path.
   */
  pragma[noinline]
  private predicate localFlowBigStep(Node node1, Node node2, Configuration config) {
    localFlowStepPlus(node1, node2, config) and
    localFlowExit(node2, config)
  }

  private module FlowDispatch {

    /**
     * Holds if the set of viable implementations that can be called by `ma`
     * might be improved by knowing the call context. This is the case if the
     * qualifier is the `i`th parameter of the enclosing callable `c`.
     */
    private predicate benefitsFromCallContext(MethodAccess ma, Callable c, int i) {
      exists(Parameter p |
        2 <= strictcount(viableImpl(ma)) and
        ma.getQualifier().(VarAccess).getVariable() = p and
        p.getPosition() = i and
        c.getAParameter() = p and
        not p.isVarargs() and
        c = ma.getEnclosingCallable()
      )
    }

    /**
     * Holds if the call `ctx` might act as a context that improves the set of
     * dispatch targets of a `MethodAccess` that occurs in a viable target of
     * `ctx`.
     */
    pragma[nomagic]
    private predicate relevantContext(Call ctx, int i) {
      exists(Callable c |
        benefitsFromCallContext(_, c, i) and
        c = viableCallable(ctx)
      )
    }

    /**
     * Holds if the `i`th argument of `ctx` has type `t` and `ctx` is a
     * relevant call context.
     */
    private predicate contextArgHasType(Call ctx, int i, RefType t, boolean exact) {
      exists(Expr arg, Expr src |
        relevantContext(ctx, i) and
        ctx.getArgument(i) = arg and
        src = variableTrack(arg) and
        exists(RefType srctype | srctype = src.getType() |
          exists(TypeVariable v | v = srctype |
            t = v.getUpperBoundType+() and not t instanceof TypeVariable
          ) or
          t = srctype and not srctype instanceof TypeVariable
        ) and
        if src instanceof ClassInstanceExpr then exact = true else exact = false
      )
    }

    /**
     * Gets a viable dispatch target of `ma` in the context `ctx`. This is
     * restricted to those `ma`s for which a context might make a difference.
     */
    cached
    private Method viableImplInCallContext(MethodAccess ma, Call ctx) {
      result = viableImpl(ma) and
      exists(int i, Callable c, Method def, RefType t, boolean exact |
        benefitsFromCallContext(ma, c, i) and
        c = viableCallable(ctx) and
        contextArgHasType(ctx, i, t, exact) and
        ma.getMethod() = def
        |
        exact = true and result = exactMethodImpl(def, t.getSourceDeclaration())
        or
        exact = false and
        exists(RefType t2 |
          result = viableMethodImpl(def, t.getSourceDeclaration(), t2) and
          not failsUnification(t, t2)
        )
      )
    }

    pragma[noinline]
    private predicate unificationTargetLeft(ParameterizedType t1, GenericType g) {
      contextArgHasType(_, _, t1, _) and t1.getGenericType() = g
    }

    pragma[noinline]
    private predicate unificationTargetRight(ParameterizedType t2, GenericType g) {
      exists(viableMethodImpl(_, _, t2)) and t2.getGenericType() = g
    }

    private predicate unificationTargets(Type t1, Type t2) {
      exists(GenericType g | unificationTargetLeft(t1, g) and unificationTargetRight(t2, g)) or
      exists(Array a1, Array a2 |
        unificationTargets(a1, a2) and
        t1 = a1.getComponentType() and
        t2 = a2.getComponentType()
      ) or
      exists(ParameterizedType pt1, ParameterizedType pt2, int pos |
        unificationTargets(pt1, pt2) and
        not pt1.getSourceDeclaration() != pt2.getSourceDeclaration() and
        t1 = pt1.getTypeArgument(pos) and
        t2 = pt2.getTypeArgument(pos)
      )
    }

    pragma[noinline]
    private predicate typeArgsOfUnificationTargets(ParameterizedType t1, ParameterizedType t2, int pos, RefType arg1, RefType arg2) {
      unificationTargets(t1, t2) and
      arg1 = t1.getTypeArgument(pos) and
      arg2 = t2.getTypeArgument(pos)
    }

    private predicate failsUnification(Type t1, Type t2) {
      unificationTargets(t1, t2) and
      (
        exists(RefType arg1, RefType arg2 |
          typeArgsOfUnificationTargets(t1, t2, _, arg1, arg2) and
          failsUnification(arg1, arg2)
        ) or
        failsUnification(t1.(Array).getComponentType(), t2.(Array).getComponentType()) or
        not (
          t1 instanceof Array and t2 instanceof Array or
          t1.(PrimitiveType) = t2.(PrimitiveType) or
          t1.(Class).getSourceDeclaration() = t2.(Class).getSourceDeclaration() or
          t1.(Interface).getSourceDeclaration() = t2.(Interface).getSourceDeclaration() or
          t1 instanceof BoundedType and t2 instanceof RefType or
          t1 instanceof RefType and t2 instanceof BoundedType
        )
      )
    }

    /**
     * Holds if the call context `ctx` reduces the set of viable dispatch
     * targets of `ma` in `c`.
     */
    predicate reducedViableImplInCallContext(MethodAccess ma, Callable c, Call ctx) {
      exists(int tgts, int ctxtgts |
        benefitsFromCallContext(ma, c, _) and
        c = viableCallable(ctx) and
        ctxtgts = count(viableImplInCallContext(ma, ctx)) and
        tgts = strictcount(viableImpl(ma)) and
        ctxtgts < tgts
      )
    }

    /**
     * Gets a viable dispatch target of `ma` in the context `ctx`. This is
     * restricted to those `ma`s for which the context makes a difference.
     */
    Method prunedViableImplInCallContext(MethodAccess ma, Call ctx) {
      result = viableImplInCallContext(ma, ctx) and
      reducedViableImplInCallContext(ma, _, ctx)
    }

    /**
     * Holds if data might flow from `ma` to a return statement in some
     * configuration.
     */
    private predicate maybeChainedReturn(MethodAccess ma) {
      exists(ReturnStmt ret |
        exists(ret.getResult()) and
        ret.getEnclosingCallable() = ma.getEnclosingCallable() and
        not ma.getParent() instanceof ExprStmt
      )
    }

    /**
     * Holds if flow returning from `m` to `ma` might return further and if
     * this path restricts the set of call sites that can be returned to.
     */
    predicate reducedViableImplInReturn(Method m, MethodAccess ma) {
      exists(int tgts, int ctxtgts |
        benefitsFromCallContext(ma, _, _) and
        m = viableImpl(ma) and
        ctxtgts = count(Call ctx | m = viableImplInCallContext(ma, ctx)) and
        tgts = strictcount(Call ctx | viableCallable(ctx) = ma.getEnclosingCallable()) and
        ctxtgts < tgts
      ) and
      maybeChainedReturn(ma)
    }

    /**
     * Gets a viable dispatch target of `ma` in the context `ctx`. This is
     * restricted to those `ma`s and results for which the return flow from the
     * result to `ma` restricts the possible context `ctx`.
     */
    Method prunedViableImplInCallContextReverse(MethodAccess ma, Call ctx) {
      result = viableImplInCallContext(ma, ctx) and
      reducedViableImplInReturn(result, ma)
    }

  }
  private import FlowDispatch

  private newtype TCallContext =
    TAnyCallContext() or
    TSpecificCall(Call call, int i) { reducedViableImplInCallContext(_, _, call) and exists(call.getArgument(i)) } or
    TSomeCall(Parameter p) or
    TReturn(Method m, MethodAccess ma) { reducedViableImplInReturn(m, ma) }

  /**
   * A call context to restrict the targets of virtual dispatch and match the
   * call sites of flow into a method with flow out of a method.
   *
   * There are four cases:
   * - `TAnyCallContext()` : No restrictions on method flow.
   * - `TSpecificCall(Call call, int i)` : Flow entered through the `i`th
   *    parameter at the given `call`. This call improves the set of viable
   *    dispatch targets for at least one method call in the current callable.
   * - `TSomeCall(Parameter p)` : Flow entered through parameter `p`. The
   *    originating call does not improve the set of dispatch targets for any
   *    method call in the current callable and was therefore not recorded.
   * - `TReturn(Method m, MethodAccess ma)` : Flow reached `ma` from `m` and
   *    this dispatch target of `ma` implies a reduced set of dispatch origins
   *    to which data may flow if it should reach a `return` statement.
   */
  private abstract class CallContext extends TCallContext {
    string toString() { result = "call context" }
  }
  private class CallContextAny extends CallContext, TAnyCallContext { }
  private abstract class CallContextCall extends CallContext { }
  private class CallContextSpecificCall extends CallContextCall, TSpecificCall { }
  private class CallContextSomeCall extends CallContextCall, TSomeCall { }
  private class CallContextReturn extends CallContext, TReturn { }

  bindingset[cc, m]
  private predicate resolveReturn(CallContext cc, Method m, MethodAccess ma) {
    cc instanceof CallContextAny and m = viableImpl(ma)
    or
    exists(Method m0, MethodAccess ma0 |
      ma0.getEnclosingCallable() = m and
      cc = TReturn(m0, ma0) and
      m0 = prunedViableImplInCallContextReverse(ma0, ma)
    )
  }

  bindingset[call, cc]
  private Callable resolveCall(Call call, CallContext cc) {
    exists(Call ctx | cc = TSpecificCall(ctx, _) |
      if reducedViableImplInCallContext(call, _, ctx) then
        result = prunedViableImplInCallContext(call, ctx)
      else
        result = viableCallable(call)
    ) or
    result = viableCallable(call) and cc instanceof CallContextSomeCall or
    result = viableCallable(call) and cc instanceof CallContextAny or
    result = viableCallable(call) and cc instanceof CallContextReturn
  }

  /**
   * Holds if data may flow from `source` to `node`. The last step in or out of
   * a callable is recorded by `cc`.
   */
  private predicate flowsTo(Node source, Node node, CallContext cc, Configuration config) {
    nodeCand(node, config) and
    (
      config.isSource(source) and
      source = node and
      cc instanceof CallContextAny
      or
      exists(Node mid |
        flowsTo(source, mid, cc, config) and
        localFlowBigStep(mid, node, config)
      )
      or
      exists(Node mid |
        flowsTo(source, mid, _, config) and
        jumpStep(mid, node) and
        cc instanceof CallContextAny
      )
      or
      flowIntoCallable(source, node.asParameter(), _, cc, _, config)
      or
      flowOutOfMethod(source, node.asExpr(), cc, config)
      or
      flowThroughMethod(source, node.asExpr(), cc, config)
    )
  }

  /**
   * Holds if data may flow from `source` to an exit of `m` in the context
   * `innercc`, and the path did not flow through a parameter of `m`.
   */
  private predicate flowOutOfMethod0(Node source, Method m, CallContext innercc, Configuration config) {
    exists(ReturnNode ret |
      flowsTo(source, ret, innercc, config) and
      m = ret.getEnclosingCallable() and
      not innercc instanceof CallContextCall
    )
  }

  /**
   * Holds if data may flow from `source` to `ma`. The last step of this path
   * is a return from a method and is recorded by `cc`, if needed.
   */
  pragma[noinline]
  private predicate flowOutOfMethod(Node source, MethodAccess ma, CallContext cc, Configuration config) {
    exists(Method m, CallContext innercc |
      flowOutOfMethod0(source, m, innercc, config) and
      resolveReturn(innercc, m, ma)
      |
      if reducedViableImplInReturn(m, ma) then cc = TReturn(m, ma) else cc = TAnyCallContext()
    )
  }

  /**
   * Holds if data may flow from `source` to the `i`th argument of `call` in `cc`.
   */
  pragma[noinline]
  private predicate flowIntoArg(Node source, int i, CallContext cc, Call call, Configuration config) {
    exists(ArgumentNode arg |
      flowsTo(source, arg, cc, config) and
      arg.argumentOf(call, i)
    )
  }

  pragma[nomagic]
  private predicate flowIntoCallable0(Node source, Callable callable, int i, CallContext outercc, Call call, Configuration config) {
    flowIntoArg(source, i, outercc, call, config) and
    callable = resolveCall(call, outercc)
  }

  /**
   * Holds if data may flow from `source` to `p` through `call`. The contexts
   * before and after entering the callable are `outercc` and `innercc`,
   * respectively.
   */
  private predicate flowIntoCallable(Node source, Parameter p, CallContext outercc, CallContextCall innercc, Call call, Configuration config) {
    exists(int i, Callable callable |
      flowIntoCallable0(source, callable, i, outercc, call, config) and
      callable.getParameter(i) = p
      |
      if reducedViableImplInCallContext(_, callable, call) then innercc = TSpecificCall(call, i) else innercc = TSomeCall(p)
    )
  }

  /** Holds if data may flow from `p` to a return statement in the callable. */
  private predicate paramFlowsThrough(Parameter p, CallContextCall cc, Configuration config) {
    exists(ReturnNode ret |
      flowsTo(_, ret, cc, config)
      |
      cc = TSomeCall(p) or
      exists(int i | cc = TSpecificCall(_, i) |
        p = ret.getEnclosingCallable().getParameter(i)
      )
    )
  }

  /**
   * Holds if data may flow from `source` to an argument of `methodcall`,
   * through a called method `m`, and back out through a return statement in
   * `m`. The context `cc` is restored to its value prior to entering `m`.
   */
  pragma[noinline]
  private predicate flowThroughMethod(Node source, Call methodcall, CallContext cc, Configuration config) {
    exists(Parameter p, CallContext innercc |
      flowIntoCallable(source, p, cc, innercc, methodcall, config) and
      paramFlowsThrough(p, innercc, config)
    )
  }

  /**
   * Holds if data can flow (inter-procedurally) from `source` to `sink`.
   *
   * Will only have results if `configuration` has non-empty sources and
   * sinks, and more sinks than sources.
   */
  predicate flowsTo(Node source, Node sink, Configuration configuration) {
    exists(Node node |
      flowsTo(source, node, _, configuration) and
      (node = sink or localFlowStepPlus(node, sink, configuration)) and
      configuration.isSink(sink)
    )
  }
}
