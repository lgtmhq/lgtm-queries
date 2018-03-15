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
 * @name User-controlled bypass of security check
 * @description Conditions that the user controls are not suited for making security-related decisions.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @id js/user-controlled-bypass
 * @tags security
 *       external/cwe/cwe-807
 *       external/cwe/cwe-290
 */
import javascript
import semmle.javascript.security.dataflow.ConditionalBypass

/**
 * A comparison that guards a sensitive action, e.g. the comparison in:
 * `var ok = x == y; if (ok) login()`.
 */
class SensitiveActionGuardComparison extends Comparison {

  SensitiveActionGuardConditional guard;

  SensitiveActionGuardComparison() {
    this = guard.asExpr().(DataFlowNode).getALocalSource()
  }

  /**
   * Gets the guard that uses this comparison.
   */
  SensitiveActionGuardConditional getGuard() {
    result = guard
  }

}

/**
 * An intermediary sink to enable reuse of the taint configuration.
 * This sink should not be presented to the client of this query.
 */
class SensitiveActionGuardComparisonOperand extends ConditionalBypassSink {

  SensitiveActionGuardComparison comparison;

  SensitiveActionGuardComparisonOperand() {
    asExpr() = comparison.getAnOperand()
  }

  override SensitiveAction getAction() {
    result = comparison.getGuard().getAction()
  }

}

/**
 * Holds if `sink` guards `action`, and `source` taints `sink`.
 *
 * If flow from `source` taints `sink`, then an attacker can
 * control if `action` should be executed or not.
 */
predicate isTaintedGuardForSensitiveAction(ConditionalBypassSink sink, DataFlow::Node source, SensitiveAction action) {
  action = sink.getAction() and
  // exclude the intermediary sink
  not sink instanceof SensitiveActionGuardComparisonOperand and
  exists (ConditionalBypassDataFlowConfiguration cfg  |
    // ordinary taint tracking to a guard
    cfg.flowsFrom(sink, source) or
    // taint tracking to both operands of a guard comparison
    exists (SensitiveActionGuardComparison cmp, DataFlow::Node lSource, DataFlow::Node rSource |
      sink = cmp.getGuard() and
      cfg.flowsFrom(DataFlow::valueNode(cmp.getLeftOperand()), lSource) and
      cfg.flowsFrom(DataFlow::valueNode(cmp.getRightOperand()), rSource) |
      source = lSource or
      source = rSource
    )
  )
}

from DataFlow::Node source, DataFlow::Node sink, SensitiveAction action
where isTaintedGuardForSensitiveAction(sink, source, action)
select sink, "This condition guards a sensitive $@, but $@ controls it.",
    action, "action",
    source, "a user-provided value"
