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
 * A simplified copy of `Tracking.qll` that implements forward-tracking
 * of `TrackedNode`s without barriers or additional flow steps.
 */
private module NodeTracking {
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
  private predicate hasForwardFlow(Function f, SsaDefinition def) {
    exists (DataFlow::Node arg, SimpleParameter p |
      argumentPassing(_, arg, f, p) and def.(SsaExplicitDefinition).getDef() = p |
      forwardFlowFromInput(_, _, arg) or
      flowsTo(_, arg, _)
    )
    or
    exists (DataFlow::SsaDefinitionNode previousDef |
      defOfCapturedVar(previousDef.getSsaVariable().getDefinition(), def, f) |
      forwardFlowFromInput(_, _, previousDef) or
      flowsTo(_, previousDef, _)
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
  private predicate forwardFlowFromInput(Function f, SsaDefinition def, DataFlow::Node sink) {
    hasForwardFlow(f, def) and
    (
      sink = DataFlow::ssaDefinitionNode(def)
      or
      exists (DataFlow::Node mid | forwardFlowFromInput(f, def, mid) |
        mid = sink.getAPredecessor()
        or
        forwardFlowThroughCall(mid, sink)
      )
    )
  }

  /**
   * Holds if function `f` returns an expression into which `def`, which is either a parameter
   * of `f` or a variable captured by `f`, flows under `configuration`, possibly through callees.
   */
  private predicate forwardReturnOfInput(Function f, SsaDefinition def) {
    exists (DataFlow::ValueNode ret |
      ret.asExpr() = f.getAReturnedExpr() and
      forwardFlowFromInput(f, def, ret)
    )
  }

  /**
   * Holds if `invk` is an invocation of a function such that `arg` is either passed as an argument
   * or captured by the function, and may flow into the function's return value under `configuration`.
   *
   * Flow is tracked forward.
   */
  private predicate forwardFlowThroughCall(DataFlow::Node arg, DataFlow::Node invk) {
    exists (Function g, SsaDefinition ssa |
      argumentPassing(invk, arg, g, ssa.(SsaExplicitDefinition).getDef()) or
      defOfCapturedVar(arg.(DataFlow::SsaDefinitionNode).getSsaVariable().getDefinition(), ssa, g) and calls(invk.asExpr(), g) |
      forwardReturnOfInput(g, ssa)
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
                                             boolean stepIn) {
    exists (AnalyzedPropertyWrite pw, DataFlow::Node mid |
      flowsTo(source, mid, stepIn) and
      pw.writes(obj, prop, mid)
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
  predicate flowsTo(TrackedNode source, DataFlow::Node sink, boolean stepIn) {
    (
      // Base case
      sink = source and
      stepIn = false
      or
      // Local flow
      exists (DataFlow::Node mid |
        flowsTo(source, mid, stepIn) and
        mid = sink.getAPredecessor()
      )
      or
      // Flow through properties of object literals
      exists (AbstractObjectLiteral obj, string prop, AnalyzedPropertyAccess read |
        forwardReachableProperty(source, obj, prop, stepIn) and
        read.reads(obj, prop) and
        sink = read
      )
      or
      // Flow into function
      exists (DataFlow::Node arg, SimpleParameter parm |
        flowsTo(source, arg, _) and
        argumentPassing(_, arg, _, parm) and sink = DataFlow::parameterNode(parm) and
        stepIn = true
      )
      or
      // Flow through a function that returns a value that depends on one of its arguments
      // or a captured variable
      exists(DataFlow::Node arg |
        flowsTo(source, arg, stepIn) and
        forwardFlowThroughCall(arg, sink)
      )
      or
      // Flow out of function
      // This path is only enabled if the flow so far did not involve
      // any interprocedural steps from an argument to a caller.
      exists (DataFlow::ValueNode invk, DataFlow::ValueNode ret, Function f |
        ret.asExpr() = f.getAReturnedExpr() and
        flowsTo(source, ret, stepIn) and stepIn = false and
        calls(invk.asExpr(), f) and
        sink = invk
      )
    )
  }
}