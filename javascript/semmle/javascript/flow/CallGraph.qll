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
 * A call graph builder based on intra-procedural data flow.
 */

import semmle.javascript.Expr
import Analysis
private import AbstractValuesImpl
private import InferredTypes

/** Entry point for call graph construction. */
class CallSite extends InvokeExpr {
  private AbstractValue getACalleeValue() {
    result = getCallee().(AnalysedFlowNode).getAValue()
  }

  Function getACallee() {
    getACalleeValue() = TAbstractFunction(result)
  }

  /**
   * Is our approximation of possible callees for this call site likely
   * to be imprecise?
   *
   * We currently track one specific source of imprecision: call
   * resolution relies on flow through global variables, and the flow
   * analysis finds possible callees that are not functions.
   * This usually means that a global variable is used in multiple
   * independent contexts, so tracking flow through it leads to
   * imprecision.
   */
  predicate isImprecise() {
    getACalleeValue().isIndefinite("global") and
    getACalleeValue().(DefiniteAbstractValue).getType() != TTFunction()
  }

  /**
   * Is our approximation of possible callees for this call site likely
   * to be incomplete?
   */
  predicate isIncomplete() {
    // the flow analysis identifies a source of incompleteness other than
    // global flow (which usually leads to imprecision rather than incompleteness)
    any (DataFlowIncompleteness cause | getACalleeValue().isIndefinite(cause)) != "global"
  }

  /**
   * Is our approximation of possible callees for this call site likely
   * to be imprecise or incomplete?
   */
  predicate isUncertain() {
    isImprecise() or isIncomplete()
  }
}