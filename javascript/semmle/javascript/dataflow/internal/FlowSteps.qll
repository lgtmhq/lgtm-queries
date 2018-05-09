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
 * INTERNAL: Do not use directly.
 *
 * Provides auxiliary predicates for defining inter-procedural data flow configurations.
 */

import javascript

/**
 * Holds if flow should be tracked through properties of `obj`.
 *
 * Flow is tracked through object literals, `module` and `module.exports` objects.
 */
predicate shouldTrackProperties(AbstractValue obj) {
  obj instanceof AbstractExportsObject or
  obj instanceof AbstractModuleObject or
  obj instanceof AbstractObjectLiteral
}

/**
 * Holds if `invk` may invoke `f`.
 */
predicate calls(InvokeExpr invk, Function f) {
  exists (CallSite cs | cs = invk |
    if cs.isIndefinite("global") then
      (f = cs.getACallee() and f.getFile() = invk.getFile())
    else
      f = cs.getACallee()
  )
}

/**
 * Holds if `f` captures the variable defined by `def` in `cap`.
 */
cached
predicate captures(Function f, SsaExplicitDefinition def, SsaVariableCapture cap) {
  def.getSourceVariable() = cap.getSourceVariable() and
  f = cap.getContainer()
}

/**
 * Holds if `source` corresponds to an expression returned by `f`, and
 * `sink` equals `source`.
 */
pragma[noinline]
predicate returnExpr(Function f, DataFlow::Node source, DataFlow::Node sink) {
  sink.asExpr() = f.getAReturnedExpr() and source = sink
}

/**
 * Holds if data can flow in one step from `pred` to `succ`,  taking
 * additional steps from the configuration into account.
 */
pragma[inline]
predicate localFlowStep(DataFlow::Node pred, DataFlow::Node succ,
                        DataFlow::Configuration configuration) {
 pred = succ.getAPredecessor()
 or
 any(DataFlow::AdditionalFlowStep afs).step(pred, succ)
 or
 configuration.isAdditionalFlowStep(pred, succ)
}

/**
 * Holds if `arg` is passed as an argument into parameter `parm`
 * through invocation `invk` of function `f`.
 */
predicate argumentPassing(DataFlow::ValueNode invk, DataFlow::ValueNode arg, Function f, SimpleParameter parm) {
  exists (int i, CallSite cs |
    cs = invk.asExpr() and calls(cs, f) and
    f.getParameter(i) = parm and not parm.isRestParameter() and
    arg = cs.getArgumentNode(i)
  )
}


/**
 * Holds if there is a flow step from `pred` to `succ` through parameter passing
 * to a function call.
 */
predicate callStep(DataFlow::Node pred, DataFlow::Node succ) {
  exists (SimpleParameter parm |
    argumentPassing(_, pred, _, parm) and
    succ = DataFlow::parameterNode(parm)
  )
}

/**
 * Holds if there is a flow step from `pred` to `succ` through returning
 * from a function call.
 */
predicate returnStep(DataFlow::Node pred, DataFlow::Node succ) {
  exists (Function f |
    returnExpr(f, pred, _) and
    calls(succ.asExpr(), f)
  )
}

/**
 * Holds if there is an assignment to property `prop` of an object represented by `obj`
 * with right hand side `rhs` somewhere, and properties of `obj` should be tracked.
 */
pragma[noinline]
private predicate trackedPropertyWrite(AbstractValue obj, string prop, DataFlow::Node rhs) {
  exists (AnalyzedPropertyWrite pw |
    pw.writes(obj, prop, rhs) and
    shouldTrackProperties(obj)
  )
}

/**
 * Holds if there is a flow step from `pred` to `succ` through an object property.
 */
predicate propertyFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
  exists (AbstractValue obj, string prop |
    trackedPropertyWrite(obj, prop, pred) and
    succ.(AnalyzedPropertyRead).reads(obj, prop)
  )
}

/**
 * A classification of flow steps:
 *
 *   - An "up" step leads from the `return` statement of a function to a call
 *     of that function.
 *   - A "down" step that leads from an argument to a function call to the
 *     corresponding parameter.
 *   - A "level" step that goes from a predecessor node to a successor node
 *     either without involving function calls at all, or via a sequence
 *     of matched function calls and returns.
 */
newtype FlowDirection = Up() or Down() or Level()

/**
 * Gets the "step-in" flag of a path that has flag `oldStepIn` if it is extended by
 * a flow step in direction `dir`: level steps do not change the flag, down steps make
 * it `true`, and up steps keep the flag `false`.
 *
 * Note that `stepIn(true, Up())` is _not_ defined; this prevents us from extending
 * paths already containing a down step with an up step and thereby losing precision.
 */
bindingset[oldStepIn]
boolean stepIn(boolean oldStepIn, FlowDirection dir) {
  dir = Level() and result = oldStepIn
  or
  dir = Down() and result = true
  or
  // only allow return steps if `stepIn` is false
  dir = Up() and oldStepIn = false and result = false
}
