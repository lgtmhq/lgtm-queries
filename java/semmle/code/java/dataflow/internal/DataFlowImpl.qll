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

/**
 * Provides an implementation of global (interprocedural) data flow. This file
 * re-exports the local (intraprocedural) data flow analysis from `DataFlowUtil`
 * and adds a global analysis, mainly exposed through the `Configuration` class.
 * This file exists in several identical copies, allowing queries to use
 * multiple `Configuration` classes that depend on each other without
 * introducing mutual recursion among those configurations.
 */

  import DataFlowUtil
  private import DataFlowPrivate
  private import DataFlowDispatch

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

    /** Holds if data flow through `node` is prohibited. */
    predicate isBarrier(Node node) { none() }

    /** Holds if data flow from `node1` to `node2` is prohibited. */
    predicate isBarrierEdge(Node node1, Node node2) { none() }

    /**
     * Holds if the additional flow step from `node1` to `node2` must be taken
     * into account in the analysis.
     */
    predicate isAdditionalFlowStep(Node node1, Node node2) { none() }

    /**
     * Holds if data may flow from `source` to `sink` for this configuration.
     */
    predicate hasFlow(Node source, Node sink) {
      flowsTo(source, sink, this)
    }

    /**
     * Holds if data may flow from `source` to `sink` for this configuration.
     *
     * The corresponding paths are generated from the end-points and the graph
     * included in the module `PathGraph`.
     */
    predicate hasFlowPath(PathNode source, PathNode sink) {
      flowsTo(source, sink, _, _, this)
    }

    /**
     * Holds if data may flow from some source to `sink` for this configuration.
     */
    predicate hasFlowTo(Node sink) {
      hasFlow(_, sink)
    }

    /**
     * Holds if data may flow from some source to `sink` for this configuration.
     */
    predicate hasFlowToExpr(Expr sink) {
      hasFlowTo(exprNode(sink))
    }

    /** DEPRECATED: use `hasFlow` instead. */
    deprecated predicate hasFlowForward(Node source, Node sink) {
      hasFlow(source, sink)
    }

    /** DEPRECATED: use `hasFlow` instead. */
    deprecated predicate hasFlowBackward(Node source, Node sink) {
      hasFlow(source, sink)
    }
  }

  /**
   * Holds if the additional step from `node1` to `node2` jumps between callables.
   */
  private predicate additionalJumpStep(Node node1, Node node2, Configuration config) {
    config.isAdditionalFlowStep(node1, node2) and
    node1.getEnclosingCallable() != node2.getEnclosingCallable()
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a static field or
   * variable capture.
   */
  private predicate jumpStep(Node node1, Node node2, Configuration config) {
    jumpStep(node1, node2) or
    additionalJumpStep(node1, node2, config)
  }

  pragma[noinline]
  private predicate isAdditionalFlowStep(Node node1, Node node2, Callable callable1, Callable callable2, Configuration config) {
    config.isAdditionalFlowStep(node1, node2) and
    callable1 = node1.getEnclosingCallable() and
    callable2 = node2.getEnclosingCallable()
  }

  /**
   * Holds if data can flow in one local step from `node1` to `node2` taking
   * additional steps from the configuration into account.
   */
  private predicate localFlowStep(Node node1, Node node2, Configuration config) {
    localFlowStep(node1, node2) and
    not config.isBarrierEdge(node1, node2)
    or
    exists(Callable callable |
      isAdditionalFlowStep(node1, node2, callable, callable, config)
    )
  }

  /**
   * Holds if `p` is the `i`th parameter of a viable dispatch target of `call`.
   * The instance parameter is considered to have index `-1`.
   */
  pragma[nomagic]
  private predicate viableParam(Call call, int i, ParameterNode p) {
    exists(Callable callable |
      callable = viableCallable(call) and
      p.isParameterOf(callable, i)
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

  pragma[noinline]
  private Callable returnNodeGetEnclosingCallable(ReturnNode ret) {
    result = ret.getEnclosingCallable()
  }

  /**
   * Holds if `node` is reachable from a source in the given configuration
   * ignoring call contexts.
   */
  private predicate nodeCandFwd1(Node node, Configuration config) {
    not config.isBarrier(node) and
    (
      config.isSource(node)
      or
      exists(Node mid |
        nodeCandFwd1(mid, config) and
        localFlowStep(mid, node, config)
      )
      or
      exists(Node mid |
        nodeCandFwd1(mid, config) and
        jumpStep(mid, node, config)
      )
      or
      // flow into a callable
      exists(Node arg |
        nodeCandFwd1(arg, config) and
        viableParamArg(node, arg)
      )
      or
      // flow out of a callable
      exists(Method m, MethodAccess ma, ReturnNode ret |
        nodeCandFwd1(ret, config) and
        m = returnNodeGetEnclosingCallable(ret) and
        m = viableImpl(ma) and
        node.asExpr() = ma
      )
    )
  }

  /**
   * Holds if `node` is part of a path from a source to a sink in the given
   * configuration ignoring call contexts.
   */
  pragma[nomagic]
  private predicate nodeCand1(Node node, Configuration config) {
    nodeCandFwd1(node, unbind(config)) and
    (
      config.isSink(node)
      or
      exists(Node mid |
        localFlowStep(node, mid, config) and
        nodeCand1(mid, config)
      )
      or
      exists(Node mid |
        jumpStep(node, mid, config) and
        nodeCand1(mid, config)
      )
      or
      // flow into a callable
      exists(Node param |
        viableParamArg(param, node) and
        nodeCand1(param, config)
      )
      or
      // flow out of a callable
      exists(Method m, ExprNode ma |
        nodeCand1(ma, config) and
        m = returnNodeGetEnclosingCallable(node) and
        m = viableImpl(ma.getExpr())
      )
    )
  }

  /**
   * Holds if there is a path from `p` to `node` in the same callable that is
   * part of a path from a source to a sink taking simple call contexts into
   * consideration.
   */
  pragma[nomagic]
  private predicate simpleParameterFlow(ParameterNode p, Node node, Configuration config) {
    nodeCand1(node, config) and
    p = node
    or
    nodeCand1(node, unbind(config)) and
    exists(Node mid |
      simpleParameterFlow(p, mid, config) and
      localFlowStep(mid, node, config)
    )
    or
    // flow through a callable
    nodeCand1(node, config) and
    exists(Node arg |
      simpleParameterFlow(p, arg, config) and
      simpleArgumentFlowsThrough(arg, node, config)
    )
  }

  /**
   * Holds if data can flow from `arg` through the `call` taking simple call
   * contexts into consideration and that this is part of a path from a source
   * to a sink.
   */
  private predicate simpleArgumentFlowsThrough(ArgumentNode arg, ExprNode call, Configuration config) {
    exists(ParameterNode param, ReturnNode ret |
      nodeCand1(arg, unbind(config)) and
      nodeCand1(call, unbind(config)) and
      viableParamArg(param, arg) and
      simpleParameterFlow(param, ret, config) and
      arg.argumentOf(call.getExpr(), _)
    )
  }

  /**
   * Holds if `node` is part of a path from a source to a sink in the given
   * configuration taking simple call contexts into consideration.
   */
  private predicate nodeCandFwd2(Node node, boolean fromArg, Configuration config) {
    nodeCand1(node, config) and
    config.isSource(node) and fromArg = false
    or
    nodeCand1(node, unbind(config)) and
    exists(Node mid |
      nodeCandFwd2(mid, fromArg, config) and
      localFlowStep(mid, node, config)
    )
    or
    nodeCand1(node, config) and
    exists(Node mid |
      nodeCandFwd2(mid, _, config) and
      jumpStep(mid, node, config) and
      fromArg = false
    )
    or
    // flow into a callable
    nodeCand1(node, config) and
    exists(Node arg |
      nodeCandFwd2(arg, _, config) and
      viableParamArg(node, arg) and
      fromArg = true
    )
    or
    // flow out of a callable
    nodeCand1(node, config) and
    exists(Method m, MethodAccess ma, ReturnNode ret |
      nodeCandFwd2(ret, false, config) and
      m = returnNodeGetEnclosingCallable(ret) and
      m = viableImpl(ma) and
      node.asExpr() = ma and
      fromArg = false
    )
    or
    // flow through a callable
    nodeCand1(node, config) and
    exists(ArgumentNode arg |
      nodeCandFwd2(arg, fromArg, config) and
      simpleArgumentFlowsThrough(arg, node, config)
    )
  }

  /**
   * Holds if `node` is part of a path from a source to a sink in the given
   * configuration taking simple call contexts into consideration.
   */
  private predicate nodeCand2(Node node, boolean toReturn, Configuration config) {
    nodeCandFwd2(node, _, config) and
    config.isSink(node) and toReturn = false
    or
    nodeCandFwd2(node, _, unbind(config)) and
    exists(Node mid |
      localFlowStep(node, mid, config) and
      nodeCand2(mid, toReturn, config)
    )
    or
    nodeCandFwd2(node, _, config) and
    exists(Node mid |
      jumpStep(node, mid, config) and
      nodeCand2(mid, _, config) and
      toReturn = false
    )
    or
    // flow into a callable
    nodeCandFwd2(node, _, unbind(config)) and
    exists(Node param |
      viableParamArg(param, node) and
      nodeCand2(param, false, config) and
      toReturn = false
    )
    or
    // flow out of a callable
    nodeCandFwd2(node, _, config) and
    exists(Method m, ExprNode ma |
      nodeCand2(ma, _, config) and
      toReturn = true and
      m = returnNodeGetEnclosingCallable(node) and
      m = viableImpl(ma.getExpr())
    )
    or
    // flow through a callable
    nodeCandFwd2(node, _, config) and
    exists(Node call |
      simpleArgumentFlowsThrough(node, call, config) and
      nodeCand2(call, toReturn, config)
    )
  }

  private predicate nodeCand(Node node, Configuration config) {
    nodeCand2(node, _, config)
  }

  /**
   * Holds if `node` can be the first node in a maximal subsequence of local
   * flow steps in a dataflow path.
   */
  private predicate localFlowEntry(Node node, Configuration config) {
    nodeCand(node, config) and
    (
      config.isSource(node) or
      jumpStep(_, node, config) or
      node instanceof ParameterNode or
      node.asExpr() instanceof MethodAccess
    )
  }

  /**
   * Holds if `node` can be the last node in a maximal subsequence of local
   * flow steps in a dataflow path.
   */
  predicate localFlowExit(Node node, Configuration config) {
    jumpStep(node, _, config) or
    node instanceof ArgumentNode or
    node instanceof ReturnNode
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
    node1 != node2 and
    nodeCand(node2, unbind(config))
    or
    exists(Node mid |
      localFlowStepPlus(node1, mid, config) and
      localFlowStep(mid, node2, config) and
      nodeCand(node2, unbind(config))
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

  /**
   * Holds if `call` passes an implicit or explicit instance argument, i.e., an
   * expression that reaches a `this` parameter.
   */
  private predicate callHasInstanceArgument(Call call) {
    exists(ArgumentNode arg |
      arg.argumentOf(call, -1)
    )
  }

  private newtype TCallContext =
    TAnyCallContext() or
    TSpecificCall(Call call, int i) {
      reducedViableImplInCallContext(_, _, call) and
      (exists(call.getArgument(i))
       or
       i = -1 and callHasInstanceArgument(call))
    } or
    TSomeCall(ParameterNode p) or
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
   * - `TSomeCall(ParameterNode p)` : Flow entered through parameter `p`. The
   *    originating call does not improve the set of dispatch targets for any
   *    method call in the current callable and was therefore not recorded.
   * - `TReturn(Method m, MethodAccess ma)` : Flow reached `ma` from `m` and
   *    this dispatch target of `ma` implies a reduced set of dispatch origins
   *    to which data may flow if it should reach a `return` statement.
   */
  private abstract class CallContext extends TCallContext {
    abstract string toString();
  }
  private class CallContextAny extends CallContext, TAnyCallContext {
    string toString() { result = "CcAny" }
  }
  private abstract class CallContextCall extends CallContext { }
  private class CallContextSpecificCall extends CallContextCall, TSpecificCall {
    string toString() { result = "CcCall" }
  }
  private class CallContextSomeCall extends CallContextCall, TSomeCall {
    string toString() { result = "CcSomeCall" }
  }
  private class CallContextReturn extends CallContext, TReturn {
    string toString() { result = "CcReturn" }
  }

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

  private bindingset[conf, result] Configuration unbind(Configuration conf) { result >= conf and result <= conf }

  private newtype TPathNode =
    TPathNodeMid(Node node, CallContext cc, Configuration config) {
      // A PathNode is introduced by a source ...
      nodeCand(node, config) and
      config.isSource(node) and
      cc instanceof CallContextAny
      or
      // ... or a step from an existing PathNode to another node.
      exists(PathNodeMid mid |
        flowStep(mid, node, cc) and
        config = mid.getConfiguration() and
        nodeCand(node, unbind(config))
      )
    } or
    TPathNodeSink(Node node, Configuration config) {
      config.isSink(node) and
      nodeCand(node, config)
    }

  /**
   * A `Node` augmented with a call context (except for sinks) and a configuration.
   * Only those `PathNode`s that are reachable from a source are generated.
   */
  abstract class PathNode extends TPathNode {
    /** Gets a textual representation of this element. */
    string toString() { result = getNode().toString() }
    /** The source location for this element. */
    Location getLocation() { result = getNode().getLocation() }
    /** Gets the underlying `Node`. */
    abstract Node getNode();
    /** Gets the associated configuration. */
    abstract Configuration getConfiguration();
    /** Gets a successor. */
    abstract PathNode getSucc();
  }

  /**
   * Provides the query predicates needed to include a graph in a path-problem query.
   */
  module PathGraph {
    /** Holds if `(a,b)` is an edge in the graph of data flow path explanations. */
    query predicate edges(PathNode a, PathNode b) { a.getSucc() = b }
  }

  /**
   * An intermediate flow graph node. This is a triple consisting of a `Node`,
   * a `CallContext`, and a `Configuration`.
   */
  private class PathNodeMid extends PathNode, TPathNodeMid {
    Node node;
    CallContext cc;
    Configuration config;
    PathNodeMid() { this = TPathNodeMid(node, cc, config) }
    override Node getNode() { result = node }
    CallContext getCallContext() { result = cc }
    override Configuration getConfiguration() { result = config }
    private PathNodeMid getSuccMid() {
      flowStep(this, result.getNode(), result.getCallContext()) and
      result.getConfiguration() = unbind(this.getConfiguration())
    }
    override PathNode getSucc() {
      // an intermediate step to another intermediate node
      result = getSuccMid()
      or
      // a final step to a sink via one or more local steps
      localFlowStepPlus(node, result.getNode(), config) and
      result instanceof PathNodeSink and
      result.getConfiguration() = unbind(this.getConfiguration())
      or
      // a final step to a sink via zero steps means we merge the last two steps to prevent trivial-looking edges
      exists(PathNodeMid mid |
        mid = getSuccMid() and
        mid.getNode() = result.getNode() and
        result instanceof PathNodeSink and
        result.getConfiguration() = unbind(mid.getConfiguration())
      )
      or
      // a direct step from a source to a sink if a node is both
      this instanceof PathNodeSource and
      result instanceof PathNodeSink and
      this.getNode() = result.getNode() and
      result.getConfiguration() = unbind(this.getConfiguration())
    }
  }

  /**
   * A flow graph node corresponding to a source.
   */
  private class PathNodeSource extends PathNodeMid {
    PathNodeSource() {
      getConfiguration().isSource(getNode()) and
      getCallContext() instanceof CallContextAny
    }
  }

  /**
   * A flow graph node corresponding to a sink. This is disjoint from the
   * intermediate nodes in order to uniquely correspond to a given sink by
   * excluding the `CallContext`.
   */
  private class PathNodeSink extends PathNode, TPathNodeSink {
    Node node;
    Configuration config;
    PathNodeSink() { this = TPathNodeSink(node, config) }
    override Node getNode() { result = node }
    override Configuration getConfiguration() { result = config }
    override PathNode getSucc() { none() }
  }

  /**
   * Holds if data may flow from `mid` to `node`. The last step in or out of
   * a callable is recorded by `cc`.
   */
  private predicate flowStep(PathNodeMid mid, Node node, CallContext cc) {
    cc = mid.getCallContext() and
    localFlowBigStep(mid.getNode(), node, mid.getConfiguration())
    or
    jumpStep(mid.getNode(), node, mid.getConfiguration()) and
    cc instanceof CallContextAny
    or
    flowIntoCallable(mid, node, _, cc, _)
    or
    flowOutOfMethod(mid, node.asExpr(), cc)
    or
    flowThroughMethod(mid, node.asExpr(), cc)
  }

  /**
   * Holds if data may flow from `mid` to an exit of `m` in the context
   * `innercc`, and the path did not flow through a parameter of `m`.
   */
  private predicate flowOutOfMethod0(PathNodeMid mid, Method m, CallContext innercc) {
    exists(ReturnNode ret |
      ret = mid.getNode() and
      innercc = mid.getCallContext() and
      m = ret.getEnclosingCallable() and
      not innercc instanceof CallContextCall
    )
  }

  /**
   * Holds if data may flow from `mid` to `ma`. The last step of this path
   * is a return from a method and is recorded by `cc`, if needed.
   */
  pragma[noinline]
  private predicate flowOutOfMethod(PathNodeMid mid, MethodAccess ma, CallContext cc) {
    exists(Method m, CallContext innercc |
      flowOutOfMethod0(mid, m, innercc) and
      resolveReturn(innercc, m, ma)
      |
      if reducedViableImplInReturn(m, ma) then cc = TReturn(m, ma) else cc = TAnyCallContext()
    )
  }

  /**
   * Holds if data may flow from `mid` to the `i`th argument of `call` in `cc`.
   */
  pragma[noinline]
  private predicate flowIntoArg(PathNodeMid mid, int i, CallContext cc, Call call) {
    exists(ArgumentNode arg |
      arg = mid.getNode() and
      cc = mid.getCallContext() and
      arg.argumentOf(call, i)
    )
  }

  pragma[noinline]
  private predicate parameterCand(Callable callable, int i, Configuration config) {
    exists(ParameterNode p |
      nodeCand(p, config) and
      p.isParameterOf(callable, i)
    )
  }

  pragma[nomagic]
  private predicate flowIntoCallable0(PathNodeMid mid, Callable callable, int i, CallContext outercc, Call call) {
    flowIntoArg(mid, i, outercc, call) and
    callable = resolveCall(call, outercc) and
    parameterCand(callable, any(int j | j <= i and j >= i), mid.getConfiguration())
  }

  /**
   * Holds if data may flow from `mid` to `p` through `call`. The contexts
   * before and after entering the callable are `outercc` and `innercc`,
   * respectively.
   */
  private predicate flowIntoCallable(PathNodeMid mid, ParameterNode p, CallContext outercc, CallContextCall innercc, Call call) {
    exists(int i, Callable callable |
      flowIntoCallable0(mid, callable, i, outercc, call) and
      p.isParameterOf(callable, i)
      |
      if reducedViableImplInCallContext(_, callable, call) then innercc = TSpecificCall(call, i) else innercc = TSomeCall(p)
    )
  }

  /** Holds if data may flow from `p` to a return statement in the callable. */
  private predicate paramFlowsThrough(ParameterNode p, CallContextCall cc, Configuration config) {
    exists(PathNodeMid mid, ReturnNode ret |
      mid.getNode() = ret and
      cc = mid.getCallContext() and
      config = mid.getConfiguration()
      |
      cc = TSomeCall(p) or
      exists(int i | cc = TSpecificCall(_, i) |
        p.isParameterOf(ret.getEnclosingCallable(), i)
      )
    )
  }

  /**
   * Holds if data may flow from `mid` to an argument of `methodcall`,
   * through a called method `m`, and back out through a return statement in
   * `m`. The context `cc` is restored to its value prior to entering `m`.
   */
  pragma[noinline]
  private predicate flowThroughMethod(PathNodeMid mid, Call methodcall, CallContext cc) {
    exists(ParameterNode p, CallContext innercc |
      flowIntoCallable(mid, p, cc, innercc, methodcall) and
      paramFlowsThrough(p, innercc, unbind(mid.getConfiguration()))
    )
  }

  /**
   * Holds if data can flow (inter-procedurally) from `source` to `sink`.
   *
   * Will only have results if `configuration` has non-empty sources and
   * sinks.
   */
  private predicate flowsTo(PathNodeSource flowsource, PathNodeSink flowsink, Node source, Node sink, Configuration configuration) {
    flowsource.getConfiguration() = configuration and
    flowsource.getNode() = source and
    flowsource.getSucc*() = flowsink and
    flowsink.getNode() = sink
  }

  /**
   * Holds if data can flow (inter-procedurally) from `source` to `sink`.
   *
   * Will only have results if `configuration` has non-empty sources and
   * sinks.
   */
  predicate flowsTo(Node source, Node sink, Configuration configuration) {
    flowsTo(_, _, source, sink, configuration)
  }
