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
 * Provides classes for performing customized data flow tracking.
 *
 * The classes in this module allow restricting the data flow analysis
 * to a particular set of source or sink nodes, and providing extra
 * edges along which flow should be propagated.
 *
 * NOTE: The API of this library is not stable yet and may change in
 *       the future.
 */

import javascript
import semmle.javascript.flow.CallGraph

/**
 * A data flow tracking configuration.
 *
 * Each use of the data flow tracking library must define its own unique extension
 * of this abstract class. A configuration defines a set of relevant sources
 * (`isSource`) and sinks (`isSink`), and may additionally
 * define additional edges beyond the standard data flow edges (`isAdditionalFlowStep`)
 * and prohibit intermediate flow nodes (`isBarrier`).
 */
abstract class FlowTrackingConfiguration extends string {
  bindingset[this]
  FlowTrackingConfiguration() { any() }

  /**
   * Holds if `source` is a relevant data flow source.
   *
   * The smaller this predicate is, the faster `flowsFrom()` will converge.
   */
  abstract predicate isSource(DataFlowNode source);

  /**
   * Holds if `sink` is a relevant data flow sink.
   *
   * The smaller this predicate is, the faster `flowsFrom()` will converge.
   */
  abstract predicate isSink(DataFlowNode sink);

  /**
   * Holds if `source -> sink` should be considered as a flow edge
   * in addition to standard data flow edges.
   */
  predicate isAdditionalFlowStep(DataFlowNode src, DataFlowNode trg) { none() }

  /**
   * Holds if the intermediate flow node `node` is prohibited.
   *
   * Note that flow through standard data flow edges cannot be prohibited.
   */
  predicate isBarrier(DataFlowNode node) { none() }

  /**
   * Holds if `source` flows to `sink`.
   *
   * The analysis searches *forwards* from the source to the sink.
   *
   * **Note**: use `flowsFrom(sink, source)` instead if the set of sinks is
   * expected to be smaller than the set of sources.
   */
  predicate flowsTo(DataFlowNode source, DataFlowNode sink) {
    flowsTo(source, sink, this, _) and
    isSink(sink)
  }

  /**
   * Holds if `source` flows to `sink`.
   *
   * The analysis searches *backwards* from the sink to the source.
   *
   * **Note**: use `flowsTo(source, sink)` instead if the set of sources is
   * expected to be smaller than the set of sinks.
   */
  predicate flowsFrom(DataFlowNode sink, DataFlowNode source) {
    flowsFrom(source, sink, this, _) and
    isSource(source)
  }
}

/**
 * Holds if `invk` may invoke `f`.
 */
private predicate calls(InvokeExpr invk, Function f) {
  exists (CallSite cs | cs = invk |
    if cs.isIndefinite("global") then
      (f = cs.getACallee() and f.getFile() = invk.getFile())
    else
      f = cs.getACallee()
  )
}

/**
 * Holds if `arg` is passed as an argument into parameter `parm`
 * through invocation `invk` of function `f`.
 */
private predicate argumentPassing(CallSite invk, Expr arg, Function f, SimpleParameter parm) {
  exists (int i |
    calls(invk, f) and
    f.getParameter(i) = parm and not parm.isRestParameter() and
    arg = invk.getArgumentNode(i)
  )
}

/**
 * Holds if `p` is a parameter of `f` that may be reached by
 * forward flow under `configuration`.
 */
private predicate hasForwardFlow(Function f, SimpleParameter p,
                                 FlowTrackingConfiguration configuration) {
  exists (Expr arg | argumentPassing(_, arg, f, p) |
    forwardParameterFlow(_, _, arg, configuration) or
    flowsTo(_, arg, configuration, _)
  )
}

/**
 * Holds if `p` is a parameter of `f` whose value flows into `sink`
 * under `configuration`, possibly through callees.
 */
private predicate forwardParameterFlow(Function f, SimpleParameter p,
                                DataFlowNode sink, FlowTrackingConfiguration configuration) {
  hasForwardFlow(f, p, configuration) and
  (
    p = f.getAParameter() and sink = p.getAnInitialUse()
    or
    exists (DataFlowNode mid | forwardParameterFlow(f, p, mid, configuration) |
      mid = sink.localFlowPred()
      or
      configuration.isAdditionalFlowStep(mid, sink)
      or
      forwardFlowThroughCall(mid, sink, configuration)
    )
  ) and
  not configuration.isBarrier(sink)
}

/**
 * Holds if the return value of `f` may be reached by
 * backward flow under `configuration`.
 */
private predicate hasBackwardFlow(Function f, FlowTrackingConfiguration configuration) {
  exists (InvokeExpr invk | argumentPassing(invk, _, f, _) |
    backwardParameterFlow(_, invk, _, configuration) or
    flowsFrom(invk, _, configuration, _)
  )
}

/**
 * Holds if the value of `source` may flow into `sink` (which is
 * an expression that may be returned from `f`), under `configuration`,
 * possibly through callees.
 */
private predicate backwardParameterFlow(Function f, DataFlowNode source,
                                DataFlowNode sink, FlowTrackingConfiguration configuration) {
  hasBackwardFlow(f, configuration) and
  (
    sink = f.getAReturnedExpr() and source = sink
    or
    exists (DataFlowNode mid | backwardParameterFlow(f, mid, sink, configuration) |
      source = mid.localFlowPred()
      or
      configuration.isAdditionalFlowStep(source, mid)
      or
      backwardFlowThroughCall(source, mid, configuration)
    )
  ) and
  not configuration.isBarrier(source)
}

/**
 * Holds if function `f` returns an expression into which its parameter `p` flows
 * under `configuration`, possibly through callees.
 */
private predicate forwardParameterReturn(Function f, SimpleParameter p, FlowTrackingConfiguration configuration) {
  forwardParameterFlow(f, p, f.getAReturnedExpr(), configuration)
}

/**
 * Holds if function `f` returns an expression into which its parameter `p` flows
 * under `configuration`, possibly through callees.
 */
private predicate backwardParameterReturn(Function f, SimpleParameter p, FlowTrackingConfiguration configuration) {
  backwardParameterFlow(f, p.getAnInitialUse(), f.getAReturnedExpr(), configuration)
}

/**
 * Holds if `arg` is passed as an argument by invocation `invk` to
 * a function such that the argument may flow into the function's
 * return value under `configuration`.
 */
private predicate forwardFlowThroughCall(Expr arg, InvokeExpr invk, FlowTrackingConfiguration configuration) {
  exists (Function g, SimpleParameter q |
    argumentPassing(invk, arg, g, q) and forwardParameterReturn(g, q, configuration)
  )
}

/**
 * Holds if `arg` is passed as an argument by invocation `invk` to
 * a function such that the argument may flow into the function's
 * return value under `configuration`.
 */
private predicate backwardFlowThroughCall(Expr arg, InvokeExpr invk, FlowTrackingConfiguration configuration) {
  exists (Function g, SimpleParameter q |
    argumentPassing(invk, arg, g, q) and backwardParameterReturn(g, q, configuration)
  )
}

/**
 * Holds if the value of `source` may flow into an assignment to property
 * `prop` of an object represented by `obj` under the given `configuration`.
 *
 * The parameter `stepIn` indicates whether steps from arguments to
 * parameters are necessary to derive this flow.
 */
pragma[noinline]
private predicate forwardReachableProperty(DataFlowNode source,
                                           AbstractObjectLiteral obj, string prop,
                                           FlowTrackingConfiguration configuration,
                                           boolean stepIn) {
  exists (AnalyzedPropertyWrite pw, DataFlowNode mid |
    flowsTo(source, mid, configuration, stepIn) and
    pw.writes(obj, prop, mid)
  )
}

/**
 * Holds if the value of property `prop` of an object represented by `obj`
 * may flow into `sink` under the given `configuration`.
 *
 * The parameter `stepOut` indicates whether steps from `return` statements to
 * invocation sites are necessary to derive this flow.
 */
pragma[noinline]
private predicate backwardReachableProperty(AbstractObjectLiteral obj, string prop,
                                            DataFlowNode sink,
                                            FlowTrackingConfiguration configuration,
                                            boolean stepOut) {
  exists (AnalyzedPropertyAccess pr |
    pr.reads(obj, prop) and
    flowsFrom(pr, sink, configuration, stepOut)
  )
}

/**
 * Holds if `source` can flow to `sink` under the given `configuration`
 * in zero or more steps.
 *
 * The parameter `stepIn` indicates whether steps from arguments to
 * parameters are necessary to derive this flow.
 */
private predicate flowsTo(DataFlowNode source, DataFlowNode sink,
                          FlowTrackingConfiguration configuration, boolean stepIn) {
  (
    // Base case
    sink = source and
    configuration.isSource(source) and
    stepIn = false
    or
    // Local flow
    exists (DataFlowNode mid |
      flowsTo(source, mid, configuration, stepIn) and
      mid = sink.localFlowPred()
    )
    or
    // Flow through properties of object literals
    exists (AbstractObjectLiteral obj, string prop, AnalyzedPropertyAccess read |
      forwardReachableProperty(source, obj, prop, configuration, stepIn) and
      read.reads(obj, prop) and
      sink = read
    )
    or
    // Flow into function
    exists (Expr arg, SimpleParameter parm |
      flowsTo(source, arg, configuration, _) and
      argumentPassing(_, arg, _, parm) and sink = parm.getAnInitialUse() and
      stepIn = true
    )
    or
    // Flow through a function that returns a value that depends on one of its arguments
    exists(Expr arg |
      flowsTo(source, arg, configuration, stepIn) and
      forwardFlowThroughCall(arg, sink, configuration)
    )
    or
    // Flow out of function
    // This path is only enabled if the flow so far did not involve
    // any interprocedural steps from an argument to a caller.
    exists (InvokeExpr invk, Function f |
      flowsTo(source, f.getAReturnedExpr(), configuration, stepIn) and stepIn = false and
      calls(invk, f) and
      sink = invk
    )
    or
    // Extra flow
    exists(DataFlowNode mid |
      flowsTo(source, mid, configuration, stepIn) and
      configuration.isAdditionalFlowStep(mid, sink)
    )
  )
  and
  not configuration.isBarrier(sink)
}

/**
 * Holds if `source` can flow to `sink` under the given `configuration`
 * in zero or more steps.
 *
 * The parameter `stepOut` indicates whether steps from `return` statements to
 * invocation sites are necessary to derive this flow.
 *
 * Unlike `flowsTo`, this predicate searches backwards from the sink
 * to the source.
 */
private predicate flowsFrom(DataFlowNode source, DataFlowNode sink,
                            FlowTrackingConfiguration configuration, boolean stepOut) {
  (
    // Base case
    sink = source and
    configuration.isSink(sink) and
    stepOut = false
    or
    // Local flow
    exists (DataFlowNode mid |
      flowsFrom(mid, sink, configuration, stepOut) and
      source = mid.localFlowPred()
    )
    or
    // Flow through properties of object literals
    exists (AbstractObjectLiteral obj, string prop, AnalyzedPropertyWrite pw |
      backwardReachableProperty(obj, prop, sink, configuration, stepOut) and
      pw.writes(obj, prop, source)
    )
    or
    // Flow into function
    // This path is only enabled if the flow so far did not involve
    // any interprocedural steps from a `return` statement to the invocation site.
    exists (SimpleParameter p |
      flowsFrom(p.getAnInitialUse(), sink, configuration, stepOut) and
      stepOut = false and
      argumentPassing(_, source, _, p)
    )
    or
    // Flow through a function that returns a value that depends on one of its arguments
    exists(InvokeExpr invk |
      flowsFrom(invk, sink, configuration, stepOut) and
      backwardFlowThroughCall(source, invk, configuration)
    )
    or
    // Flow out of function
    exists (InvokeExpr invk, Function f |
      flowsFrom(invk, sink, configuration, _) and
      calls(invk, f) and
      source = f.getAReturnedExpr() and
      stepOut = true
    )
    or
    // Extra flow
    exists (DataFlowNode mid |
      flowsFrom(mid, sink, configuration, stepOut) and
      configuration.isAdditionalFlowStep(source, mid)
    )
  )
  and
  not configuration.isBarrier(source)
}

/**
 * Provides classes for modelling taint propagation.
 */
module TaintTracking {
  /**
   * A data flow tracking configuration that considers taint propagation through
   * objects, arrays, promises and strings in addition to standard data flow.
   *
   * If a different set of flow edges is desired, extend this class and override
   * `isAdditionalTaintStep`.
   */
  abstract class Configuration extends FlowTrackingConfiguration {
    bindingset[this]
    Configuration() { any() }

    /**
     * Holds if `source` is a relevant taint source.
     *
     * The smaller this predicate is, the faster `hasFlow()` will converge.
     */
    // overridden to provide taint-tracking specific qldoc
    abstract override predicate isSource(DataFlowNode source);

    /**
     * Holds if `sink` is a relevant taint sink.
     *
     * The smaller this predicate is, the faster `hasFlow()` will converge.
     */
    // overridden to provide taint-tracking specific qldoc
    abstract override predicate isSink(DataFlowNode sink);

    /** Holds if the intermediate node `node` is a taint sanitizer. */
    predicate isSanitizer(DataFlowNode node) {
      sanitizedByGuard(this, node)
    }

    final
    override predicate isBarrier(DataFlowNode node) { isSanitizer(node) }

    /**
     * Holds if the additional taint propagation step from `pred` to `succ`
     * must be taken into account in the analysis.
     */
    predicate isAdditionalTaintStep(DataFlowNode pred, DataFlowNode succ) {
      pred = succ.(FlowTarget).getATaintSource()
    }

    final
    override predicate isAdditionalFlowStep(DataFlowNode pred, DataFlowNode succ) {
      isAdditionalTaintStep(pred, succ)
    }
  }

  /**
   * Holds if variable use `u` is sanitized for the purposes of taint-tracking
   * configuration `cfg`.
   */
  private predicate sanitizedByGuard(Configuration cfg, VarUse u) {
    exists (SsaVariable v | u = v.getAUse() |
      // either `v` is a refined variable where the guard performs
      // sanitization
      exists (SsaRefinementNode ref | v = ref.getVariable() |
        guardSanitizes(cfg, ref.getGuard(), _)
      )
      or
      // or there is a non-refining guard that dominates this use
      exists (ConditionGuardNode guard |
        guardSanitizes(cfg, guard, v) and guard.dominates(u.getBasicBlock())
      )
    )
  }

  /**
   * Holds if `guard` is sanitizes `v` for the purposes of taint-tracking
   * configuration `cfg`.
   */
  private predicate guardSanitizes(Configuration cfg,
                                   ConditionGuardNode guard, SsaVariable v) {
    exists (SanitizingGuard sanitizer | sanitizer = guard.getTest() |
      sanitizer.sanitizes(cfg, guard.getOutcome(), v)
    )
  }

  /**
   * An expression that can act as a sanitizer for a variable when appearing
   * in a condition.
   */
  abstract class SanitizingGuard extends Expr {
    /**
     * Holds if this expression sanitizes variable `v` for the purposes of taint-tracking
     * configuration `cfg`, provided it evaluates to `outcome`.
     */
    abstract predicate sanitizes(Configuration cfg, boolean outcome, SsaVariable v);
  }

  /**
   * A taint propagating data flow edge, represented by its target node.
   */
  abstract class FlowTarget extends DataFlowNode {
    /** Gets another data flow node from which taint is propagated to this node. */
    abstract DataFlowNode getATaintSource();
  }

  /**
   * A taint propagating data flow edge through object or array elements and
   * promises.
   */
  private class DefaultFlowTarget extends FlowTarget {
    DefaultFlowTarget() {
      this instanceof Expr
    }

    override DataFlowNode getATaintSource() {
      // iterating over a tainted iterator taints the loop variable
      exists (EnhancedForLoop efl | result = efl.getIterationDomain() |
        this = efl.getAnIterationVariable().getAnAccess()
      )
      or
      // arrays with tainted elements and objects with tainted property names are tainted
      this.(ArrayExpr).getAnElement() = result or
      exists (Property prop | this.(ObjectExpr).getAProperty() = prop |
        prop.isComputed() and result = prop.getNameExpr()
      )
      or
      // reading from a tainted object yields a tainted result
      this.(PropAccess).getBase() = result
      or
      // awaiting a tainted expression gives a tainted result
      this.(AwaitExpr).getOperand() = result
      or
      // comparing a tainted expression against a constant gives a tainted result
      this.(Comparison).hasOperands(result, any(Expr e | exists(e.getStringValue())))
      or
      // `array.map(function (elt, i, ary) { ... })`: if `array` is tainted, then so are
      // `elt` and `ary`; similar for `forEach`
      exists (MethodCallExpr m, Function f, int i, SimpleParameter p |
        (m.getMethodName() = "map" or m.getMethodName() = "forEach") and
        (i = 0 or i = 2) and
        f = m.getArgument(0).(DataFlowNode).getALocalSource() and
        p = f.getParameter(i) and
        this = p.getAnInitialUse() and
        result = m.getReceiver()
      )
    }
  }

  /**
   * A taint propagating data flow edge for assignments of the form `o[k] = v`, where
   * `k` is not a constant and `o` refers to some object literal; in this case, we consider
   * taint to flow from `v` to any variable that refers to the object literal.
   *
   * The rationale for this heuristic is that if properties of `o` are accessed by
   * computed (that is, non-constant) names, then `o` is most likely being treated as
   * a map, not as a real object. In this case, it makes sense to consider the entire
   * map to be tainted as soon as one of its entries is.
   */
  private class DictionaryFlowTarget extends FlowTarget, @varaccess {
    DataFlowNode source;

    DictionaryFlowTarget() {
      exists (AssignExpr assgn, IndexExpr idx, ObjectExpr obj |
        assgn.getTarget() = idx and
        idx.getBase().(DataFlowNode).getALocalSource() = obj and
        not exists(idx.getPropertyName()) and
        this.(DataFlowNode).getALocalSource() = obj and
        source = assgn.getRhs()
      )
    }

    override DataFlowNode getATaintSource() {
      result = source
    }
  }

  /**
   * A taint propagating data flow edge arising from string append and other string
   * operations defined in the standard library.
   *
   * Note that since we cannot easily distinguish string append from addition, we consider
   * any `+` operation to propagate taint.
   */
  private class StringManipulationFlowTarget extends FlowTarget {
    StringManipulationFlowTarget() {
      this instanceof Expr
    }

    override DataFlowNode getATaintSource() {
      // addition propagates taint
      this.(AddExpr).getAnOperand() = result or
      this.(AssignAddExpr).getAChildExpr() = result or
      exists (SsaExplicitDefinition ssa |
        this = ssa.getVariable().getAUse() and
        result = ssa.getDef() and
        result instanceof AssignAddExpr
      )
      or
      // templating propagates taint
      this.(TemplateLiteral).getAnElement() = result
      or
      // other string operations that propagate taint
      exists (string name | name = this.(MethodCallExpr).getMethodName() |
        result = this.(MethodCallExpr).getReceiver() and
        ( // sorted, interesting, properties of String.prototype
          name = "anchor" or
          name = "big" or
          name = "blink" or
          name = "bold" or
          name = "concat" or
          name = "fixed" or
          name = "fontcolor" or
          name = "fontsize" or
          name = "italics" or
          name = "link" or
          name = "padEnd" or
          name = "padStart" or
          name = "repeat" or
          name = "replace" or
          name = "slice" or
          name = "small" or
          name = "split" or
          name = "strike" or
          name = "sub" or
          name = "substr" or
          name = "substring" or
          name = "sup" or
          name = "toLocaleLowerCase" or
          name = "toLocaleUpperCase" or
          name = "toLowerCase" or
          name = "toString" or
          name = "toUpperCase" or
          name = "trim" or
          name = "trimLeft" or
          name = "trimRight" or
          name = "valueOf"
        ) or
        exists (int i | result = this.(MethodCallExpr).getArgument(i) |
          name = "concat" or
          name = "replace" and i = 1
        )
      )
      or
      // standard library constructors that propagate taint: `RegExp` and `String`
      exists (InvokeExpr invk, string gv |
        invk = this and invk.getCallee().accessesGlobal(gv) and result = invk.getArgument(0) |
        gv = "RegExp" or gv = "String"
      )
      or
      // String.fromCharCode and String.fromCodePoint
      exists (int i, MethodCallExpr mce |
        mce = this and
        result = mce.getArgument(i) and
        (mce.getMethodName() = "fromCharCode" or mce.getMethodName() = "fromCodePoint")
      )
      or
      // `(encode|decode)URI(Component)?` and `escape` propagate taint
      exists (CallExpr c, string name |
        c = this and c.getCallee().accessesGlobal(name) and result = c.getArgument(0) |
        name = "encodeURI" or name = "decodeURI" or
        name = "encodeURIComponent" or name = "decodeURIComponent"
      )
    }
  }

  /**
   * A taint propagating data flow edge arising from JSON parsing or unparsing.
   */
  private class JsonManipulationFlowTarget extends FlowTarget, @callexpr {
    JsonManipulationFlowTarget() {
      exists (MethodCallExpr mce, string methodName |
        mce = this and methodName = mce.getMethodName() |
        mce.getReceiver().accessesGlobal("JSON") and
        (methodName = "parse" or methodName = "stringify")
      )
    }

    override DataFlowNode getATaintSource() {
      result = this.(CallExpr).getArgument(0)
    }
  }

  /**
   * Holds if `params` is a `URLSearchParams` object providing access to
   * the parameters encoded in `input`.
   */
  predicate isUrlSearchParams(DataFlowNode params, DataFlowNode input) {
    exists (NewExpr urlSearchParams | urlSearchParams = params |
      urlSearchParams.getCallee().accessesGlobal("URLSearchParams") and
      input = urlSearchParams.getArgument(0)
    )
    or
    exists (NewExpr url, DataFlowNode recv |
      params.(PropAccess).accesses(recv, "searchParams") and
      recv.getALocalSource() = url and
      url.getCallee().accessesGlobal("URL") and
      input = url.getArgument(0)
    )
  }

  /**
   * A taint propagating data flow edge arising from URL parameter parsing.
   */
  private class UrlSearchParamsFlowTarget extends FlowTarget {
    DataFlowNode source;

    UrlSearchParamsFlowTarget() {
      // either this is itself an `URLSearchParams` object
      isUrlSearchParams(this, source)
      or
      // or this is a call to `get` or `getAll` on a `URLSearchParams` object
      exists (DataFlowNode recv, string m |
        this.(MethodCallExpr).calls(recv, m) and
        isUrlSearchParams(recv.getALocalSource(), source) and
        m.matches("get%")
      )
    }

    override DataFlowNode getATaintSource() {
      result = source
    }
  }
}
