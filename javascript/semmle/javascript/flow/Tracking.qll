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
private import semmle.javascript.flow.InferredTypes

/**
 * A data flow tracking configuration.
 *
 * Each use of the data flow tracking library must define its own unique extension
 * of this abstract class. A configuration defines a set of relevant sources
 * (`isSource`) and sinks (`isSink`), and may additionally
 * define additional edges beyond the standard data flow edges (`isAdditionalFlowStep`)
 * and prohibit intermediate flow nodes and edges (`isBarrier`).
 */
abstract class FlowTrackingConfiguration extends string {
  bindingset[this]
  FlowTrackingConfiguration() { any() }

  /**
   * Holds if `source` is a relevant data flow source.
   *
   * The smaller this predicate is, the faster `flowsFrom()` will converge.
   */
  abstract predicate isSource(DataFlow::Node source);

  /**
   * Holds if `sink` is a relevant data flow sink.
   *
   * The smaller this predicate is, the faster `flowsFrom()` will converge.
   */
  abstract predicate isSink(DataFlow::Node sink);

  /**
   * Holds if `source -> sink` should be considered as a flow edge
   * in addition to standard data flow edges.
   */
  predicate isAdditionalFlowStep(DataFlow::Node src, DataFlow::Node trg) { none() }

  /**
   * Holds if the intermediate flow node `node` is prohibited.
   */
  predicate isBarrier(DataFlow::Node node) { none() }

  /**
   * Holds if flow from `src` to `trg` is prohibited.
   */
  predicate isBarrier(DataFlow::Node src, DataFlow::Node trg) { none() }

  /**
   * Holds if `source` flows to `sink`.
   *
   * The analysis searches *forwards* from the source to the sink.
   *
   * **Note**: use `flowsFrom(sink, source)` instead if the set of sinks is
   * expected to be smaller than the set of sources.
   */
  predicate flowsTo(DataFlow::Node source, DataFlow::Node sink) {
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
  predicate flowsFrom(DataFlow::Node sink, DataFlow::Node source) {
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
 * Holds if data can flow in one step from `src` to `trg`,  taking
 * additional steps and barriers from the configuration into account.
 */
pragma[inline]
private predicate localFlowStep(DataFlow::Node src, DataFlow::Node trg,
                                FlowTrackingConfiguration configuration) {
  (src = trg.getAPredecessor() or configuration.isAdditionalFlowStep(src, trg)) and
  not configuration.isBarrier(src, trg)
}


/**
 * Holds if `arg` is passed as an argument into parameter `parm`
 * through invocation `invk` of function `f`.
 */
private predicate argumentPassing(DataFlow::ValueNode invk, DataFlow::ValueNode arg, Function f, SimpleParameter parm) {
  exists (int i, CallSite cs |
    cs = invk.asExpr() and calls(cs, f) and
    f.getParameter(i) = parm and not parm.isRestParameter() and
    arg = cs.getArgumentNode(i)
  )
}

/**
 * Holds if `def` is a parameter of `f` or a variable that is captured
 * by `f`, such that `def` may be reached by forward flow under `configuration`.
 */
private predicate hasForwardFlow(Function f, SsaDefinition def,
                                 FlowTrackingConfiguration configuration) {
  exists (DataFlow::Node arg, SimpleParameter p |
    argumentPassing(_, arg, f, p) and def.(SsaExplicitDefinition).getDef() = p |
    forwardFlowFromInput(_, _, arg, configuration) or
    flowsTo(_, arg, configuration, _)
  )
  or
  exists (DataFlow::SsaDefinitionNode previousDef |
    defOfCapturedVar(previousDef.getSsaVariable().getDefinition(), def, f) |
    forwardFlowFromInput(_, _, previousDef, configuration) or
    flowsTo(_, previousDef, configuration, _)
  )
}

/**
 * Holds if `expl` is a definition of the variable captured by `f` in `cap`.
 */
private predicate defOfCapturedVar(SsaExplicitDefinition expl, SsaVariableCapture cap, Function f) {
  expl.getSourceVariable() = cap.getSourceVariable() and
  f = cap.getContainer()
}

/**
 * Holds if `def` is a parameter of `f` or a variable that is captured
 * by `f` whose value flows into `sink` under `configuration`, possibly through callees.
 */
private predicate forwardFlowFromInput(Function f, SsaDefinition def,
                                       DataFlow::Node sink, FlowTrackingConfiguration configuration) {
  hasForwardFlow(f, def, configuration) and
  (
    sink = DataFlow::ssaDefinitionNode(def)
    or
    exists (DataFlow::Node mid | forwardFlowFromInput(f, def, mid, configuration) |
      localFlowStep(mid, sink, configuration)
      or
      forwardFlowThroughCall(mid, sink, configuration) and
      not configuration.isBarrier(mid, sink)
    )
  ) and
  not configuration.isBarrier(sink)
}

/**
 * Holds if the return value of `f` may be reached by
 * backward flow under `configuration`.
 */
private predicate hasBackwardFlow(Function f, FlowTrackingConfiguration configuration) {
  exists (DataFlow::Node invk | calls(invk.asExpr(), f) |
    backwardFlowFromInput(_, invk, _, configuration) or
    flowsFrom(invk, _, configuration, _)
  )
}

/**
 * Holds if the value of `source` may flow into `sink` (which is
 * an expression that may be returned from `f`), under `configuration`,
 * possibly through callees.
 */
private predicate backwardFlowFromInput(Function f, DataFlow::Node source,
                                        DataFlow::ValueNode sink, FlowTrackingConfiguration configuration) {
  hasBackwardFlow(f, configuration) and
  (
    sink.asExpr() = f.getAReturnedExpr() and source = sink
    or
    exists (DataFlow::Node mid | backwardFlowFromInput(f, mid, sink, configuration) |
      localFlowStep(source, mid, configuration)
      or
      backwardFlowThroughCall(source, mid, configuration) and
      not configuration.isBarrier(source, mid)
    )
  ) and
  not configuration.isBarrier(source)
}

/**
 * Holds if function `f` returns an expression into which `def`, which is either a parameter
 * of `f` or a variable captured by `f`, flows under `configuration`, possibly through callees.
 */
private predicate forwardReturnOfInput(Function f, SsaDefinition def, FlowTrackingConfiguration configuration) {
  exists (DataFlow::ValueNode ret |
    ret.asExpr() = f.getAReturnedExpr() and
    forwardFlowFromInput(f, def, ret, configuration)
  )
}

/**
 * Holds if function `f` returns an expression into which `def`, which is either a parameter
 * of `f` or a variable captured by `f`, flows under `configuration`, possibly through callees.
 */
private predicate backwardReturnOfInput(Function f, SsaDefinition def, FlowTrackingConfiguration configuration) {
  exists (DataFlow::ValueNode ret |
    ret.asExpr() = f.getAReturnedExpr() and
    backwardFlowFromInput(f, DataFlow::ssaDefinitionNode(def), ret, configuration)
  )
}

/**
 * Holds if `invk` is an invocation of a function such that `arg` is either passed as an argument
 * or captured by the function, and may flow into the function's return value under `configuration`.
 *
 * Flow is tracked forward.
 */
private predicate forwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk, FlowTrackingConfiguration configuration) {
  exists (Function g, SsaDefinition ssa |
    argumentPassing(invk, arg, g, ssa.(SsaExplicitDefinition).getDef()) or
    defOfCapturedVar(arg.(DataFlow::SsaDefinitionNode).getSsaVariable().getDefinition(), ssa, g) and calls(invk.asExpr(), g) |
    forwardReturnOfInput(g, ssa, configuration)
  )
}

/**
 * Holds if `invk` is an invocation of a function such that `arg` is either passed as an argument
 * or captured by the function, and may flow into the function's return value under `configuration`.
 *
 * Flow is tracked backward.
 */
private predicate backwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk, FlowTrackingConfiguration configuration) {
  exists (Function g, SsaDefinition ssa |
    argumentPassing(invk, arg, g,  ssa.(SsaExplicitDefinition).getDef()) or
    defOfCapturedVar(arg.(DataFlow::SsaDefinitionNode).getSsaVariable().getDefinition(), ssa, g) and calls(invk.asExpr(), g) |
    backwardReturnOfInput(g, ssa, configuration)
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
private predicate forwardReachableProperty(DataFlow::Node source,
                                           AbstractObjectLiteral obj, string prop,
                                           FlowTrackingConfiguration configuration,
                                           boolean stepIn) {
  exists (AnalyzedPropertyWrite pw, DataFlow::Node mid |
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
                                            DataFlow::Node sink,
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
pragma[nomagic]
private predicate flowsTo(DataFlow::Node source, DataFlow::Node sink,
                          FlowTrackingConfiguration configuration, boolean stepIn) {
  (
    // Base case
    sink = source and
    configuration.isSource(source) and
    stepIn = false
    or
    // Local flow
    exists (DataFlow::Node mid |
      flowsTo(source, mid, configuration, stepIn) and
      localFlowStep(mid, sink, configuration)
    )
    or
    // Flow through properties of object literals
    exists (AbstractObjectLiteral obj, string prop, AnalyzedPropertyAccess read |
      forwardReachableProperty(source, obj, prop, configuration, stepIn) and
      read.reads(obj, prop) and
      sink = read and
      not configuration.isBarrier(source, sink)
    )
    or
    // Flow into function
    exists (DataFlow::Node arg, SimpleParameter parm |
      flowsTo(source, arg, configuration, _) and
      argumentPassing(_, arg, _, parm) and sink = DataFlow::parameterNode(parm) and
      not configuration.isBarrier(arg, sink) and
      stepIn = true
    )
    or
    // Flow through a function that returns a value that depends on one of its arguments
    // or a captured variable
    exists(DataFlow::Node arg |
      flowsTo(source, arg, configuration, stepIn) and
      forwardFlowThroughCall(arg, sink, configuration) and
      not configuration.isBarrier(arg, sink)
    )
    or
    // Flow out of function
    // This path is only enabled if the flow so far did not involve
    // any interprocedural steps from an argument to a caller.
    exists (DataFlow::ValueNode invk, DataFlow::ValueNode ret, Function f |
      ret.asExpr() = f.getAReturnedExpr() and
      flowsTo(source, ret, configuration, stepIn) and stepIn = false and
      calls(invk.asExpr(), f) and
      sink = invk and
      not configuration.isBarrier(ret, sink)
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
pragma[nomagic]
private predicate flowsFrom(DataFlow::Node source, DataFlow::Node sink,
                            FlowTrackingConfiguration configuration, boolean stepOut) {
  (
    // Base case
    sink = source and
    configuration.isSink(sink) and
    stepOut = false
    or
    // Local flow
    exists (DataFlow::Node mid |
      flowsFrom(mid, sink, configuration, stepOut) and
      localFlowStep(source, mid, configuration)
    )
    or
    // Flow through properties of object literals
    exists (AbstractObjectLiteral obj, string prop, AnalyzedPropertyWrite pw |
      backwardReachableProperty(obj, prop, sink, configuration, stepOut) and
      pw.writes(obj, prop, source) and
      not configuration.isBarrier(source, sink)
    )
    or
    // Flow into function
    // This path is only enabled if the flow so far did not involve
    // any interprocedural steps from a `return` statement to the invocation site.
    exists (SimpleParameter p |
      flowsFrom(DataFlow::parameterNode(p), sink, configuration, stepOut) and
      stepOut = false and
      argumentPassing(_, source, _, p) and
      not configuration.isBarrier(source, DataFlow::parameterNode(p))
    )
    or
    // Flow through a function that returns a value that depends on one of its arguments
    // or a captured variable
    exists(DataFlow::Node invk |
      flowsFrom(invk, sink, configuration, stepOut) and
      backwardFlowThroughCall(source, invk, configuration) and
      not configuration.isBarrier(source, invk)
    )
    or
    // Flow out of function
    exists (DataFlow::ValueNode invk, Function f |
      flowsFrom(invk, sink, configuration, _) and
      calls(invk.asExpr(), f) and
      source.asExpr() = f.getAReturnedExpr() and
      not configuration.isBarrier(source, invk) and
      stepOut = true
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
    abstract override predicate isSource(DataFlow::Node source);

    /**
     * Holds if `sink` is a relevant taint sink.
     *
     * The smaller this predicate is, the faster `hasFlow()` will converge.
     */
    // overridden to provide taint-tracking specific qldoc
    abstract override predicate isSink(DataFlow::Node sink);

    /** Holds if the intermediate node `node` is a taint sanitizer. */
    predicate isSanitizer(DataFlow::Node node) {
      sanitizedByGuard(this, node)
    }

    /** Holds if the edge from `source` to `sink` is a taint sanitizer. */
    predicate isSanitizer(DataFlow::Node source, DataFlow::Node sink) {
      none()
    }

    final
    override predicate isBarrier(DataFlow::Node node) { isSanitizer(node) }

    final
    override predicate isBarrier(DataFlow::Node source, DataFlow::Node sink) {
      isSanitizer(source, sink)
    }

    /**
     * Holds if the additional taint propagation step from `pred` to `succ`
     * must be taken into account in the analysis.
     */
    predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
      pred = succ.(FlowTarget).getATaintSource()
    }

    final
    override predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
      isAdditionalTaintStep(pred, succ)
    }
  }

  /**
   * Holds if data flow node `nd` acts as a sanitizer for the purposes of taint-tracking
   * configuration `cfg`.
   */
  private predicate sanitizedByGuard(Configuration cfg, DataFlow::Node nd) {
    exists (SsaRefinementNode ref |
      nd = DataFlow::ssaDefinitionNode(ref) and
      forex (SsaVariable input | input = ref.getAnInput() |
        guardSanitizes(cfg, ref.getGuard(), input)
      )
    )
    or
    // or there is a non-refining guard that dominates this use
    exists (SsaVariable ssa, BasicBlock bb |
      nd = DataFlow::valueNode(ssa.getAUseIn(bb)) and
      exists (ConditionGuardNode guard |
        guardSanitizes(cfg, guard, ssa) and
        guard.dominates(bb)
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
  abstract class FlowTarget extends DataFlow::Node {
    /** Gets another data flow node from which taint is propagated to this node. */
    abstract DataFlow::Node getATaintSource();
  }

  /**
   * A taint propagating data flow edge through object or array elements and
   * promises.
   */
  private class DefaultFlowTarget extends FlowTarget {
    DefaultFlowTarget() {
      this = DataFlow::valueNode(_) or
      this = DataFlow::parameterNode(_)
    }

    override DataFlow::ValueNode getATaintSource() {
      exists (Expr e, Expr f | e = this.asExpr() and f = result.asExpr() |
        // iterating over a tainted iterator taints the loop variable
        exists (EnhancedForLoop efl | f = efl.getIterationDomain() |
          e = efl.getAnIterationVariable().getAnAccess()
        )
        or
        // arrays with tainted elements and objects with tainted property names are tainted
        e.(ArrayExpr).getAnElement() = f or
        exists (Property prop | e.(ObjectExpr).getAProperty() = prop |
          prop.isComputed() and f = prop.getNameExpr()
        )
        or
        // reading from a tainted object yields a tainted result
        e.(PropAccess).getBase() = f
        or
        // awaiting a tainted expression gives a tainted result
        e.(AwaitExpr).getOperand() = f
        or
        // comparing a tainted expression against a constant gives a tainted result
        e.(Comparison).hasOperands(f, any(ConstantString cs))
      )
      or
      // `array.map(function (elt, i, ary) { ... })`: if `array` is tainted, then so are
      // `elt` and `ary`; similar for `forEach`
      exists (MethodCallExpr m, Function f, int i, SimpleParameter p |
        (m.getMethodName() = "map" or m.getMethodName() = "forEach") and
        (i = 0 or i = 2) and
        f = m.getArgument(0).(DataFlowNode).getALocalSource() and
        p = f.getParameter(i) and
        this = DataFlow::parameterNode(p) and
        result.asExpr() = m.getReceiver()
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
  private class DictionaryFlowTarget extends FlowTarget, DataFlow::ValueNode {
    DataFlow::Node source;

    DictionaryFlowTarget() {
      asExpr() instanceof VarAccess and
      exists (AssignExpr assgn, IndexExpr idx, ObjectExpr obj |
        assgn.getTarget() = idx and
        idx.getBase().(DataFlowNode).getALocalSource() = obj and
        not exists(idx.getPropertyName()) and
        astNode.(DataFlowNode).getALocalSource() = obj and
        source = DataFlow::valueNode(assgn.getRhs())
      )
    }

    override DataFlow::Node getATaintSource() {
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
  private class StringManipulationFlowTarget extends FlowTarget, DataFlow::ValueNode {
    override DataFlow::Node getATaintSource() {
      // addition propagates taint
      astNode.(AddExpr).getAnOperand() = result.asExpr() or
      astNode.(AssignAddExpr).getAChildExpr() = result.asExpr() or
      exists (SsaExplicitDefinition ssa |
        astNode = ssa.getVariable().getAUse() and
        result.asExpr().(AssignAddExpr) = ssa.getDef()
      )
      or
      // templating propagates taint
      astNode.(TemplateLiteral).getAnElement() = result.asExpr()
      or
      // other string operations that propagate taint
      exists (string name | name = astNode.(MethodCallExpr).getMethodName() |
        result.asExpr() = astNode.(MethodCallExpr).getReceiver() and
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
        exists (int i | result.asExpr() = astNode.(MethodCallExpr).getArgument(i) |
          name = "concat" or
          name = "replace" and i = 1
        )
      )
      or
      // standard library constructors that propagate taint: `RegExp` and `String`
      exists (InvokeExpr invk, string gv |
        invk = astNode and
        invk.getCallee().accessesGlobal(gv) and
        result = DataFlow::valueNode(invk.getArgument(0)) |
        gv = "RegExp" or gv = "String"
      )
      or
      // String.fromCharCode and String.fromCodePoint
      exists (int i, MethodCallExpr mce |
        mce = astNode and
        result.asExpr() = mce.getArgument(i) and
        (mce.getMethodName() = "fromCharCode" or mce.getMethodName() = "fromCodePoint")
      )
      or
      // `(encode|decode)URI(Component)?` and `escape` propagate taint
      exists (CallExpr c, string name |
        c = astNode and c.getCallee().accessesGlobal(name) and
        result = DataFlow::valueNode(c.getArgument(0)) |
        name = "encodeURI" or name = "decodeURI" or
        name = "encodeURIComponent" or name = "decodeURIComponent"
      )
    }
  }

  /**
   * A taint propagating data flow edge arising from JSON parsing or unparsing.
   */
  private class JsonManipulationFlowTarget extends FlowTarget, DataFlow::ValueNode {
    JsonManipulationFlowTarget() {
      exists (MethodCallExpr mce, string methodName |
        mce = astNode and methodName = mce.getMethodName() and
        mce.getReceiver().accessesGlobal("JSON") |
        methodName = "parse" or methodName = "stringify"
      )
    }

    override DataFlow::Node getATaintSource() {
      result.asExpr() = astNode.(CallExpr).getArgument(0)
    }
  }

  /**
   * Holds if `params` is a `URLSearchParams` object providing access to
   * the parameters encoded in `input`.
   */
  predicate isUrlSearchParams(DataFlow::Node params, DataFlow::Node input) {
    exists (NewExpr urlSearchParams | urlSearchParams = params.asExpr() |
      urlSearchParams.getCallee().accessesGlobal("URLSearchParams") and
      input = DataFlow::valueNode(urlSearchParams.getArgument(0))
    )
    or
    exists (NewExpr url, DataFlowNode recv |
      params.asExpr().(PropAccess).accesses(recv, "searchParams") and
      recv.getALocalSource() = url and
      url.getCallee().accessesGlobal("URL") and
      input = DataFlow::valueNode(url.getArgument(0))
    )
  }

  /**
   * A taint propagating data flow edge arising from URL parameter parsing.
   */
  private class UrlSearchParamsFlowTarget extends FlowTarget, DataFlow::ValueNode {
    DataFlow::Node source;

    UrlSearchParamsFlowTarget() {
      // either this is itself an `URLSearchParams` object
      isUrlSearchParams(this, source)
      or
      // or this is a call to `get` or `getAll` on a `URLSearchParams` object
      exists (DataFlowNode recv, string m |
        astNode.(MethodCallExpr).calls(recv, m) and
        isUrlSearchParams(DataFlow::valueNode(recv.getALocalSource()), source) and
        m.matches("get%")
      )
    }

    override DataFlow::Node getATaintSource() {
      result = source
    }
  }

  /**
   * Holds if `cfg` is any taint tracking configuration.
   *
   * This is an auxiliary predicate used in the definition of sanitizing guards
   * that intentionally do not restrict the set of configurations they apply to.
   */
  private predicate anyCfg(Configuration cfg) {
    any()
  }

  /**
   * A conditional checking a tainted string against a regular expression, which is
   * considered to be a sanitizer for all configurations.
   */
  class SanitizingRegExpTest extends SanitizingGuard, Expr {
    VarUse u;

    SanitizingRegExpTest() {
      exists (MethodCallExpr mce, DataFlowNode base, string m, DataFlowNode firstArg |
        mce = this and mce.calls(base, m) and firstArg = mce.getArgument(0) |
        // /re/.test(u) or /re/.exec(u)
        base.getALocalSource() instanceof RegExpLiteral and
        (m = "test" or m = "exec") and
        firstArg = u
        or
        // u.match(/re/) or u.match("re")
        base = u and
        m = "match" and
        (
         firstArg.getALocalSource() instanceof RegExpLiteral or
         firstArg.getALocalSource() instanceof ConstantString
        )
      )
      or
      // m = /re/.exec(u) and similar
      this.(AssignExpr).getRhs().(SanitizingRegExpTest).getSanitizedVarUse() = u
    }

    private VarUse getSanitizedVarUse() {
      result = u
    }

    override predicate sanitizes(Configuration cfg, boolean outcome, SsaVariable v) {
      anyCfg(cfg) and
      (outcome = true or outcome = false) and
      u = v.getAUse()
    }
  }

  /** A check of the form `if(o.hasOwnProperty(x))`, which sanitizes `x` in its "then" branch. */
  class HasOwnPropertySanitizer extends TaintTracking::SanitizingGuard, MethodCallExpr {
    SsaVariable x;

    HasOwnPropertySanitizer() {
      this.getMethodName() = "hasOwnProperty" and
      getArgument(0) = x.getAUse()
    }

    override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
      anyCfg(cfg) and
      outcome = true and x = v
    }
  }

  /** A check of the form `if(x in o)`, which sanitizes `x` in its "then" branch. */
  class InSanitizer extends TaintTracking::SanitizingGuard, InExpr {
    SsaVariable x;

    InSanitizer() {
      getLeftOperand() = x.getAUse()
    }

    override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
      anyCfg(cfg) and
      outcome = true and x = v
    }
  }

  /** A check of the form `if(o[x] != undefined)`, which sanitizes `x` in its "then" branch. */
  class UndefinedCheckSanitizer extends TaintTracking::SanitizingGuard, EqualityTest {
    SsaVariable x;

    UndefinedCheckSanitizer() {
      exists (IndexExpr idx, AnalyzedFlowNode undef | hasOperands(idx, undef.asExpr()) |
        // one operand is of the form `o[x]`
        idx = getAnOperand() and idx.getPropertyNameExpr() = x.getAUse() and
        // and the other one is guaranteed to be `undefined`
        undef.getTheType() = TTUndefined()
      )
    }

    override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
      anyCfg(cfg) and
      outcome = getPolarity().booleanNot() and x = v
    }
  }
}
