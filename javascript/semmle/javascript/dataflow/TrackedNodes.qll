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
 * Provides support for inter-procedural tracking of a customizable
 * set of data flow nodes.
 */

import javascript

/**
 * A data flow node that should be tracked inter-procedurally.
 *
 * To track additional values, extends this class with additional
 * subclasses.
 */
abstract class TrackedNode extends DataFlow::Node {
  /**
   * Holds if this node flows into `sink` in zero or more (possibly
   * inter-procedural) steps.
   */
  predicate flowsTo(DataFlow::Node sink) {
    NodeTracking::flowsTo(this, sink, _)
  }
}

/**
 * An expression whose value should be tracked inter-procedurally.
 *
 * To track additional expressions, extends this class with additional
 * subclasses.
 */
abstract class TrackedExpr extends Expr {
  predicate flowsTo(Expr sink) {
    exists (TrackedExprNode ten | ten.asExpr() = this |
      ten.flowsTo(DataFlow::valueNode(sink))
    )
  }
}

/**
 * Turn all `TrackedExpr`s into `TrackedNode`s.
 */
private class TrackedExprNode extends TrackedNode {
  TrackedExprNode() { asExpr() instanceof TrackedExpr }
}

/**
 * A simplified copy of `Configuration.qll` that implements forward-tracking
 * of `TrackedNode`s without barriers or additional flow steps.
 */
private module NodeTracking {
  private import internal.FlowSteps

  /**
   * Holds if data can flow in one step from `pred` to `succ`,  taking
   * additional steps into account.
   */
  pragma[inline]
  predicate localFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
   pred = succ.getAPredecessor()
   or
   any(DataFlow::AdditionalFlowStep afs).step(pred, succ)
  }

  /**
   * Holds if there is a flow step from `pred` to `succ` in direction `dir`.
   *
   * Summary steps through function calls are not taken into account.
   */
  private predicate basicFlowStep(DataFlow::Node pred, DataFlow::Node succ, FlowDirection dir) {
    isRelevant(pred) and
    (
     // Local flow
     localFlowStep(pred, succ) and
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
   * Holds if `nd` may be reachable from a tracked node.
   *
   * No call/return matching is done, so this is a relatively coarse over-approximation.
   */
  private predicate isRelevant(DataFlow::Node nd) {
    nd instanceof TrackedNode
    or
    exists (DataFlow::Node mid |
      isRelevant(mid) and
      basicFlowStep(mid, nd, _)
    )
  }

  /**
   * Holds if `def` is a parameter of `f` or a variable that is captured by `f`,
   * such that `def` may be reachable from a tracked node.
   */
  private predicate hasForwardFlow(Function f, SsaDefinition def) {
    exists (DataFlow::Node arg, SimpleParameter p |
      argumentPassing(_, arg, f, p) and
      def.(SsaExplicitDefinition).getDef() = p and
      isRelevant(arg)
    )
    or
    exists (SsaDefinition prevDef |
      captures(f, prevDef, def) and
      isRelevant(DataFlow::ssaDefinitionNode(prevDef))
    )
  }

  /**
   * Holds if function `f` returns an expression into which `def`, which is either a parameter
   * of `f` or a variable captured by `f`, flows, possibly through callees.
   */
  private predicate forwardReturnOfInput(Function f, SsaDefinition def) {
    exists (DataFlow::ValueNode ret |
      ret.asExpr() = f.getAReturnedExpr() and
      forwardFlowFromInput(f, def, ret)
    )
  }

  /**
   * Holds if `invk` is an invocation of a function such that `arg` is either passed as an argument
   * or captured by the function, and may flow into the function's return value.
   */
  private predicate forwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk) {
    exists (Function g, SsaDefinition ssa |
      argumentPassing(invk, arg, g, ssa.(SsaExplicitDefinition).getDef())
      or
      exists (SsaDefinition prevDef |
        arg = DataFlow::ssaDefinitionNode(prevDef) and
        captures(g, prevDef, ssa) and
        calls(invk.asExpr(), g)
      )
      |
      forwardReturnOfInput(g, ssa)
    )
  }

  /**
   * Holds if `def` is a parameter of `f` or a variable that is captured
   * by `f` whose value flows into `sink`, possibly through callees.
   */
  private predicate forwardFlowFromInput(Function f, SsaDefinition def, DataFlow::Node sink) {
    (
      hasForwardFlow(f, def) and
      sink = DataFlow::ssaDefinitionNode(def)
      or
      exists (DataFlow::Node mid | forwardFlowFromInput(f, def, mid) |
        localFlowStep(mid, sink)
        or
        forwardFlowThroughCall(mid, sink)
      )
    )
  }

  /**
   * Holds if there is a flow step from `pred` to `succ` in direction `dir`.
   */
  private predicate flowStep(DataFlow::Node pred, DataFlow::Node succ, FlowDirection dir) {
    basicFlowStep(pred, succ, dir)
    or
    // Flow through a function that returns a value that depends on one of its arguments
    // or a captured variable
    forwardFlowThroughCall(pred, succ) and
    dir = Level()
  }

  /**
   * Holds if there is a path from `source` to `nd`, where `stepIn` is true if that
   * path contains a down step.
   */
  predicate flowsTo(TrackedNode source, DataFlow::Node nd, boolean stepIn) {
    source = nd and
    stepIn = false
    or
    exists (DataFlow::Node pred, boolean oldStepIn, FlowDirection dir |
      flowsTo(source, pred, oldStepIn) and
      flowStep(pred, nd, dir) and
      stepIn = stepIn(oldStepIn, dir)
    )
  }
}
