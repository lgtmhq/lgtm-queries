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
 * Provides a class for performing customized inter-procedural data flow.
 *
 * The class in this module provides an interface for performing inter-procedural
 * data flow from a custom set of source nodes to a custom set of sink nodes.
 * Additional data flow edges can be specified, and conversely certain nodes or
 * edges can be designated as _barriers_ that block flow.
 *
 * NOTE: The API of this library is not stable yet and may change in
 *       the future.
 *
 *
 * # Technical overview
 *
 * This module implements a summarization-based inter-procedural data flow
 * analysis. Data flow is tracked through local variables, imports and (some)
 * object properties, as well as into and out of function calls. The latter
 * is done by computing function summaries that record which function parameters
 * and captured variables may flow into the function's return value.
 *
 * For example, for the function
 *
 * ```
 * function choice(b, x, y) {
 *   return b ? x : y;
 * }
 * ```
 *
 * we determine that its second and third (but not the first) parameter may
 * flow into its return value.
 *
 * Hence when we see a call `a = choice(b, c, d)`, we propagate flow from `c`
 * to `a` and from `d` to `a` (but not from `b` to `a`).
 *
 * The inter-procedural data flow graph is represented by class `PathNode`
 * and its member predicate `getASuccessor`. Each `PathNode` is a pair
 * of an underlying `DataFlow::Node` and a `DataFlow::Configuration`, which
 * can be accessed through member predicates `getNode` and `getConfiguration`,
 * respectively.
 *
 * # Implementation details
 *
 * Function summaries are computed by predicate `forwardFlowThroughCall`.
 * Predicate `flowStep` computes a "one-step" flow relation, where, however,
 * a single step may be based on a function summary, and hence already involve
 * inter-procedural flow.
 *
 * Flow steps are classified as being "down", "up" or "level": a down step
 * goes from a call site to a callee, an up step from a return to a caller,
 * and a level step is either a step that does not involve function calls
 * or a step through a summary.
 *
 * Predicate `reachableFromSource` computes inter-procedural paths from
 * sources along the `flowStep` relation, keeping track of whether any of
 * these steps is a down step. Up steps are only allowed if no previous
 * step was a down step to avoid confusion between different call sites.
 *
 * Predicate `onPath` builds on `reachableFromSource` to compute full
 * paths from sources to sinks, this time starting with the sinks. Similar
 * to above, it keeps track of whether any of the steps from a node to a
 * sink is an up step, and only considers down steps for paths that do
 * not contain an up step.
 *
 * Finally, we build `PathNode`s for all nodes that appear on a path
 * computed by `onPath`.
 */

import javascript
private import internal.FlowSteps

/**
 * A data flow tracking configuration for finding inter-procedural paths from
 * sources to sinks.
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
   * Holds if data may flow from `source` to `sink` for this configuration.
   */
  predicate hasFlow(DataFlow::Node source, DataFlow::Node sink) {
    exists (SourcePathNode flowsource, SinkPathNode flowsink |
      hasPathFlow(flowsource, flowsink) and
      source = flowsource.getNode() and
      sink = flowsink.getNode()
    )
  }

  /**
   * Holds if data may flow from `source` to `sink` for this configuration.
   */
  predicate hasPathFlow(SourcePathNode source, SinkPathNode sink) {
    flowsTo(source, _, sink, _, this)
  }

  /**
   * DEPRECATED: Use `hasFlow` instead.
   *
   * Holds if `source` flows to `sink`.
   */
  deprecated predicate flowsTo(DataFlow::Node source, DataFlow::Node sink) {
    hasFlow(source, sink)
  }

  /**
   * DEPRECATED: Use `hasFlow` instead.
   *
   * Holds if `source` flows to `sink`.
   */
  deprecated predicate flowsFrom(DataFlow::Node sink, DataFlow::Node source) {
    hasFlow(source, sink)
  }
}

/**
 * A data flow edge that should be added to all data flow configurations in
 * addition to standard data flow edges.
 *
 * Note: For performance reasons, all subclasses of this class should be part
 * of the standard library. Override `Configuration::isAdditionalFlowStep`
 * for analysis-specific flow steps.
 */
abstract class AdditionalFlowStep extends DataFlow::Node {
  /**
   * Holds if `pred` &rarr; `succ` should be considered a data flow edge.
   */
  abstract cached predicate step(DataFlow::Node pred, DataFlow::Node succ);
}

/**
 * Additional flow step to model flow from import specifiers into the SSA variable
 * corresponding to the imported variable.
 */
private class FlowStepThroughImport extends AdditionalFlowStep, DataFlow::ValueNode {
  override ImportSpecifier astNode;

  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists (SsaExplicitDefinition ssa |
      pred = this and
      ssa.getDef() = astNode and
      succ = DataFlow::ssaDefinitionNode(ssa)
    )
  }
}

/**
 * Holds if there is a flow step from `pred` to `succ` in direction `dir`
 * under configuration `cfg`.
 *
 * Summary steps through function calls are not taken into account.
 */
private predicate basicFlowStep(DataFlow::Node pred, DataFlow::Node succ, FlowDirection dir,
                                DataFlow::Configuration cfg) {
  isRelevant(pred, cfg) and
  (
   // Local flow
   localFlowStep(pred, succ, cfg) and
   dir = Level()
   or
   // Flow through properties of objects
   propertyFlowStep(pred, succ) and
   dir = Level()
   or
   // Flow into function
   callStep(pred, succ) and
   dir = Down()
   or
   // Flow out of function
   returnStep(pred, succ) and
   dir = Up()
  )
}

/**
 * Holds if `nd` may be reachable from a source under `cfg`. No call/return matching
 * is done, so this is a relatively coarse over-approximation.
 */
private predicate isRelevant(DataFlow::Node nd, DataFlow::Configuration cfg) {
  cfg.isSource(nd)
  or
  exists (DataFlow::Node mid |
    isRelevant(mid, cfg) and
    basicFlowStep(mid, nd, _, cfg)
  )
}

/**
 * Holds if `def` is a parameter of `f` or a variable that is captured by `f`,
 * such that `def` may be reached by forward flow under configuration `cfg`.
 */
private predicate hasForwardFlow(Function f, SsaDefinition def,
                                 DataFlow::Configuration cfg) {
  exists (DataFlow::Node arg, SimpleParameter p |
    argumentPassing(_, arg, f, p) and
    def.(SsaExplicitDefinition).getDef() = p and
    isRelevant(arg, cfg)
  )
  or
  exists (SsaDefinition prevDef |
    captures(f, prevDef, def) and
    isRelevant(DataFlow::ssaDefinitionNode(prevDef), cfg)
  )
}

/**
 * Holds if function `f` returns an expression into which `def`, which is either a parameter
 * of `f` or a variable captured by `f`, flows under configuration `cfg`, possibly through callees.
 */
private predicate forwardReturnOfInput(Function f, SsaDefinition def, DataFlow::Configuration cfg) {
  exists (DataFlow::ValueNode ret |
    ret.asExpr() = f.getAReturnedExpr() and
    forwardFlowFromInput(f, def, ret, cfg)
  )
}

/**
 * Holds if `invk` is an invocation of a function such that `arg` is either passed as an argument
 * or captured by the function, and may flow into the function's return value under configuration
 * `cfg`.
 *
 * Flow is tracked forward.
 */
private predicate forwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk, DataFlow::Configuration cfg) {
  exists (Function g, SsaDefinition ssa |
    argumentPassing(invk, arg, g, ssa.(SsaExplicitDefinition).getDef())
    or
    exists (SsaDefinition prevDef |
      arg = DataFlow::ssaDefinitionNode(prevDef) and
      captures(g, prevDef, ssa) and
      calls(invk.asExpr(), g)
    )
    |
    forwardReturnOfInput(g, ssa, cfg)
  )
}

/**
 * Holds if `def` is a parameter of `f` or a variable that is captured
 * by `f` whose value flows into `sink` under configuration `cfg`, possibly through callees.
 */
private predicate forwardFlowFromInput(Function f, SsaDefinition def,
                                       DataFlow::Node sink, DataFlow::Configuration cfg) {
  (
    hasForwardFlow(f, def, cfg) and
    sink = DataFlow::ssaDefinitionNode(def)
    or
    exists (DataFlow::Node mid | forwardFlowFromInput(f, def, mid, cfg) |
      localFlowStep(mid, sink, cfg)
      or
      forwardFlowThroughCall(mid, sink, cfg) and
      not cfg.isBarrier(mid, sink)
    )
  ) and
  not cfg.isBarrier(sink)
}

/**
 * Holds if there is a flow step from `pred` to `succ` in direction `dir`
 * under configuration `cfg`.
*/
private predicate flowStep(DataFlow::Node pred, DataFlow::Configuration cfg,
                           DataFlow::Node succ, FlowDirection dir) {
  (
   basicFlowStep(pred, succ, dir, cfg)
   or
   // Flow through a function that returns a value that depends on one of its arguments
   // or a captured variable
   forwardFlowThroughCall(pred, succ, cfg) and
   dir = Level()
  ) and
  not cfg.isBarrier(succ) and
  not cfg.isBarrier(pred, succ)
}

/**
 * Holds if `source` can flow to `sink` under configuration `cfg`
 * in zero or more steps.
 */
pragma [nomagic]
private predicate flowsTo(PathNode flowsource, DataFlow::Node source,
                          SinkPathNode flowsink, DataFlow::Node sink,
                          DataFlow::Configuration cfg) {
  flowsource = MkPathNode(source, cfg, _) and
  flowsink = flowsource.getASuccessor*() and
  flowsink = MkPathNode(sink, id(cfg), _)
}

/**
 * Holds if `nd` is reachable from a source under `cfg`. The parameter `stepIn`
 * records whether the path from the source to `nd` contains a down step.
 */
private predicate reachableFromSource(DataFlow::Node nd, DataFlow::Configuration cfg, boolean stepIn) {
  cfg.isSource(nd) and
  not cfg.isBarrier(nd) and
  stepIn = false
  or
  exists (DataFlow::Node pred, boolean oldStepIn, FlowDirection dir |
    reachableFromSource(pred, cfg, oldStepIn) and
    flowStep(pred, cfg, nd, dir) and
    stepIn = stepIn(oldStepIn, dir)
  )
}

/**
 * Gets the "step-out" flag of a path that has flag `oldStepOut` if it is extended by
 * a flow step in direction `dir`: level steps do not change the flag, up steps make
 * it `true`, and down steps keep the flag `false`.
 *
 * Note that `stepOut(true, Down())` is _not_ defined; this prevents us from extending
 * paths already containing an up step with a down step and thereby losing precision.
 */
bindingset[oldStepOut]
private boolean stepOut(boolean oldStepOut, FlowDirection dir) {
  dir = Level() and result = oldStepOut
  or
  dir = Up() and result = true
  or
  // only allow call steps if `stepOut` is false
  dir = Down() and oldStepOut = false and result = false
}

/**
 * Holds if `nd` can be reached from a source under `cfg`, and in turn a sink is
 * reachable from `nd`. The flag `stepIn` records whether a down step occurs on
 * the path from the source to `nd`, and the `stepOut` flag whether an up step
 * occurs on the path from `nd` to the sink.
 */
private predicate onPath(DataFlow::Node nd, DataFlow::Configuration cfg,
                         boolean stepIn, boolean stepOut) {
  reachableFromSource(nd, cfg, stepIn) and
  cfg.isSink(nd) and
  not cfg.isBarrier(nd) and
  stepOut = false
  or
  exists (DataFlow::Node mid, FlowDirection dir, boolean oldStepOut |
    onPath(mid, cfg, _, oldStepOut) and
    flowStep(nd, cfg, mid, dir) and
    reachableFromSource(nd, cfg, stepIn) and
    stepOut = stepOut(oldStepOut, dir)
  )
}

/**
 * A data flow node on an inter-procedural path from a source.
 */
private newtype TPathNode =
  MkPathNode(DataFlow::Node nd, DataFlow::Configuration cfg, boolean stepIn) {
    onPath(nd, cfg, stepIn, _)
  }

/**
 * Maps `cfg` to itself.
 *
 * This is an auxiliary predicate that is needed in some places to prevent us
 * from computing a cross-product of all path nodes belonging to the same configuration.
 */
bindingset[cfg, result]
private DataFlow::Configuration id(DataFlow::Configuration cfg) {
  result >= cfg and cfg >= result
}

/**
 * A data flow node on an inter-procedural path from a source to a sink.
 *
 * A path node is a triple `(nd, cfg, stepIn)` where `nd` is a data flow node and `cfg`
 * is a data flow tracking configuration such that `nd` is on a path from a source to a
 * sink under `cfg`. The `stepIn` flag records whether that path contains a down step.
 */
class PathNode extends TPathNode {
  DataFlow::Node nd;
  DataFlow::Configuration cfg;
  boolean stepIn;

  PathNode() { this = MkPathNode(nd, cfg, stepIn) }

  /** Gets the underlying data flow node of this path node. */
  DataFlow::Node getNode() {
    result = nd
  }

  /** Gets the underlying data flow tracking configuration of this path node. */
  DataFlow::Configuration getConfiguration() {
    result = cfg
  }

  /** Gets a successor node of this path node. */
  PathNode getASuccessor() {
    exists (DataFlow::Node succ, FlowDirection dir |
      flowStep(nd, id(cfg), succ, dir) and
      result = MkPathNode(succ, id(cfg), stepIn(stepIn, dir))
    )
  }

  /** Gets a textual representation of this path node. */
  string toString() {
    result = nd.toString()
  }

  /**
   * Holds if this path node is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/help/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                            int endline, int endcolumn) {
    nd.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

/**
 * A path node corresponding to a flow source.
 */
class SourcePathNode extends PathNode {
  SourcePathNode() {
    cfg.isSource(nd)
  }
}

/**
 * A path node corresponding to a flow sink.
 */
class SinkPathNode extends PathNode {
  SinkPathNode() {
    cfg.isSink(nd)
  }
}

/**
 * Provides the query predicate needed to include a graph in a path-problem query.
 */
module PathGraph {
  /** Holds if `pred` &rarr; `succ` is an edge in the graph of data flow path explanations. */
  query predicate edges(PathNode pred, PathNode succ) {
    pred.getASuccessor() = succ
  }
}
