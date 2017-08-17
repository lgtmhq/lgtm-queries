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
private predicate argumentPassing(InvokeExpr invk, Expr arg, Function f, SimpleParameter parm) {
  exists (int i |
    calls(invk, f) and
    f.getParameter(i) = parm and not parm.isRestParameter() and
    invk.getArgument(i) = arg and not invk.isSpreadArgument([0..i])
  )
}

/**
 * Gets a use of `parm` that refers to its initial value as
 * passed in from the caller.
 */
private DataFlowNode getInitialUseOfParameter(SimpleParameter parm) {
  exists (SsaExplicitDefinition parmDef |
    parmDef.getDef() = parm and
    result = parmDef.getVariable().getAUse()
  )
}

/**
 * Holds if `p` is a parameter of `f` whose value flows into `sink`
 * under `configuration`, possibly through callees.
 */
private predicate parameterFlow(Function f, SimpleParameter p,
                                DataFlowNode sink, FlowTrackingConfiguration configuration) {
  (
    p = f.getAParameter() and sink = getInitialUseOfParameter(p)
    or
    exists (DataFlowNode mid | parameterFlow(f, p, mid, configuration) |
      mid = sink.localFlowPred()
      or
      flowThroughCall(mid, sink, configuration)
    )
  ) and
  not configuration.isBarrier(sink)
}

/**
 * Holds if function `f` returns an expression into which its parameter `p` flows
 * under `configuration`, possibly through callees.
 */
private predicate parameterReturn(Function f, SimpleParameter p, FlowTrackingConfiguration configuration) {
  parameterFlow(f, p, f.getAReturnedExpr(), configuration)
}

/**
 * Holds if `arg` is passed as an argument by invocation `invk` to
 * a function such that the argument may flow into the function's
 * return value under `configuration`.
 */
private predicate flowThroughCall(Expr arg, InvokeExpr invk, FlowTrackingConfiguration configuration) {
  exists (Function g, SimpleParameter q |
    argumentPassing(invk, arg, g, q) and parameterReturn(g, q, configuration)
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
    // Flow into function
    exists (Expr arg, SimpleParameter parm |
      flowsTo(source, arg, configuration, _) and
      argumentPassing(_, arg, _, parm) and sink = getInitialUseOfParameter(parm) and
      stepIn = true
    )
    or
    // Flow through a function that returns a value that depends on one of its arguments
    exists(Expr arg |
      flowsTo(source, arg, configuration, stepIn) and
      flowThroughCall(arg, sink, configuration)
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
    // Flow into function
    // This path is only enabled if the flow so far did not involve
    // any interprocedural steps from a `return` statement to the invocation site.
    exists (SimpleParameter parm, SsaExplicitDefinition parmDef |
      parmDef.getDef() = parm and
      flowsFrom(parmDef.getVariable().getAUse(), sink, configuration, stepOut) and
      stepOut = false and
      argumentPassing(_, source, _, parm)
    )
    or
    // Flow through a function that returns a value that depends on one of its arguments
    exists(InvokeExpr invk |
      flowsFrom(invk, sink, configuration, stepOut) and
      flowThroughCall(source, invk, configuration)
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
      // arrays with tainted elements and objects with tainted properties are tainted
      this.(ArrayExpr).getAnElement() = result or
      exists (Property prop | this.(ObjectExpr).getAProperty() = prop |
        prop.isComputed() and result = prop.getNameExpr() or
        result = prop.getInit()
      )
      or
      // reading from a tainted object or with a tainted index yields a tainted result
      this.(IndexExpr).getAChildExpr() = result or
      this.(DotExpr).getBase() = result
      or
      // awaiting a tainted expression gives a tainted result
      this.(AwaitExpr).getOperand() = result
      or
      // comparing a tainted expression against a constant gives a tainted result
      this.(Comparison).hasOperands(result, any(Expr e | exists(e.getStringValue())))
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
      this.(AssignAddExpr).getAChildExpr() = result
      or
      // templating propagates taint
      this.(TemplateLiteral).getAnElement() = result
      or
      // other string operations that propagate taint
      exists (string name | name = this.(MethodCallExpr).getMethodName() |
        result = this.(MethodCallExpr).getReceiver() and
        (name = "concat" or name = "match" or name = "replace" or name = "slice" or
         name = "split" or name = "substr" or name = "substring" or
         name = "toLocaleLowerCase" or name = "toLocaleUpperCase" or
         name = "toLowerCase" or name = "toString" or name = "toUpperCase" or
         name = "trim" or name = "valueOf")
        or
        exists (int i | result = this.(MethodCallExpr).getArgument(i) |
          name = "concat" or
          name = "replace" and i = 1
        )
      )
      or
      // standard library constructors that propagate taint: `RegExp` and `String`
      exists (InvokeExpr invk, GlobalVarAccess gv |
        invk = this and gv = invk.getCallee() and result = invk.getArgument(0) |
        gv.getName() = "RegExp" or gv.getName() = "String"
      )
      or
      // regular expression operations that propagate taint
      exists (MethodCallExpr mce | mce = this |
        // RegExp.prototype.exec: from first argument to call
        mce.getReceiver().(DataFlowNode).getALocalSource() instanceof RegExpLiteral and
        mce.getMethodName() = "exec" and
        result = mce.getArgument(0)
      )
      or
      // `(encode|decode)URI(Component)?` propagate taint
      exists (CallExpr c, string name |
        c = this and accessesGlobal(c.getCallee(), name) and result = c.getArgument(0) |
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
        accessesGlobal(mce.getReceiver(), "JSON") and
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
      accessesGlobal(urlSearchParams.getCallee(), "URLSearchParams") and
      input = urlSearchParams.getArgument(0)
    )
    or
    exists (NewExpr url, DataFlowNode recv |
      params.(PropAccess).accesses(recv, "searchParams") and
      recv.getALocalSource() = url and
      accessesGlobal(url.getCallee(), "URL") and
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