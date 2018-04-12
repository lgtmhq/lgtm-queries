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
 * Provides classes for performing customized data flow.
 *
 * The classes in this module allow performing inter-procedural data flow
 * from a custom set of source nodes to a custom set of sink nodes. Additional
 * data flow edges can be specified, and conversely certain nodes or edges can
 * be designated as _barriers_ that block flow.
 *
 * NOTE: The API of this library is not stable yet and may change in
 *       the future.
 */

import javascript

/**
 * A data flow tracking configuration.
 *
 * Each use of the data flow tracking library must define its own unique extension
 * of this abstract class. A configuration defines a set of relevant sources
 * (`isSource`) and sinks (`isSink`), and may additionally
 * define additional edges beyond the standard data flow edges (`isAdditionalFlowStep`)
 * and prohibit intermediate flow nodes and edges (`isBarrier`).
 */
abstract class Configuration extends string {
  bindingset[this]
  Configuration() { any() }

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
                                Configuration configuration) {
  (
   src = trg.getAPredecessor()
   or
   // extra step: the flow analysis models import specifiers as property reads;
   // they should flow into the SSA variable corresponding to the imported variable
   flowStepThroughImport(src, trg)
   or
   configuration.isAdditionalFlowStep(src, trg)
  ) and
  not configuration.isBarrier(src, trg)
}

pragma[noinline]
private predicate flowStepThroughImport(DataFlow::Node src, DataFlow::Node trg) {
  exists (ImportSpecifier is, SsaExplicitDefinition ssa |
    src = DataFlow::valueNode(is) and
    ssa.getDef() = is and
    trg = DataFlow::ssaDefinitionNode(ssa)
  )
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
                                 Configuration configuration) {
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
                                       DataFlow::Node sink, Configuration configuration) {
  (
    hasForwardFlow(f, def, configuration) and
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
private predicate hasBackwardFlow(Function f, Configuration configuration) {
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
                                        DataFlow::ValueNode sink, Configuration configuration) {
  (
    hasBackwardFlow(f, configuration) and
    returnExpr(f, source, sink)
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

pragma[noinline]
private predicate returnExpr(Function f, DataFlow::Node source, DataFlow::Node sink) {
  sink.asExpr() = f.getAReturnedExpr() and source = sink
}

/**
 * Holds if function `f` returns an expression into which `def`, which is either a parameter
 * of `f` or a variable captured by `f`, flows under `configuration`, possibly through callees.
 */
private predicate forwardReturnOfInput(Function f, SsaDefinition def, Configuration configuration) {
  exists (DataFlow::ValueNode ret |
    ret.asExpr() = f.getAReturnedExpr() and
    forwardFlowFromInput(f, def, ret, configuration)
  )
}

/**
 * Holds if function `f` returns an expression into which `def`, which is either a parameter
 * of `f` or a variable captured by `f`, flows under `configuration`, possibly through callees.
 */
private predicate backwardReturnOfInput(Function f, SsaDefinition def, Configuration configuration) {
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
private predicate forwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk, Configuration configuration) {
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
private predicate backwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk, Configuration configuration) {
  exists (Function g, SsaDefinition ssa |
    argumentPassing(invk, arg, g,  ssa.(SsaExplicitDefinition).getDef()) or
    defOfCapturedVar(arg.(DataFlow::SsaDefinitionNode).getSsaVariable().getDefinition(), ssa, g) and calls(invk.asExpr(), g) |
    backwardReturnOfInput(g, ssa, configuration)
  )
}

/**
 * Holds if flow should be tracked through properties of `obj`.
 *
 * Currently, flow is tracked through object literals, `module` and
 * `module.exports` objects.
 */
private predicate shouldTrackProperties(AbstractValue obj) {
  obj instanceof AbstractExportsObject or
  obj instanceof AbstractModuleObject or
  obj instanceof AbstractObjectLiteral
}

/**
 * Holds if the value of `source` may flow into an assignment to property
 * `prop` of an object represented by `obj` under the given `configuration`.
 *
 * The parameter `stepIn` indicates whether steps from arguments to
 * parameters are necessary to derive this flow.
 */
pragma[nomagic]
private predicate forwardReachableProperty(DataFlow::Node source,
                                           AbstractValue obj, string prop,
                                           Configuration configuration,
                                           boolean stepIn) {
  exists (AnalyzedPropertyWrite pw, DataFlow::Node mid |
    flowsTo(source, mid, configuration, stepIn) and
    pw.writes(obj, prop, mid) and
    shouldTrackProperties(obj)
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
private predicate backwardReachableProperty(AbstractValue obj, string prop,
                                            DataFlow::Node sink,
                                            Configuration configuration,
                                            boolean stepOut) {
  exists (AnalyzedPropertyRead pr |
    pr.reads(obj, prop) and
    shouldTrackProperties(obj) and
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
                          Configuration configuration, boolean stepIn) {
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
    // Flow through properties of objects
    exists (AbstractValue obj, string prop, AnalyzedPropertyRead read |
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
                            Configuration configuration, boolean stepOut) {
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
    // Flow through properties of objects
    exists (AbstractValue obj, string prop, AnalyzedPropertyWrite pw |
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
