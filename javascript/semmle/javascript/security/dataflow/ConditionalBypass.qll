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
 * Provides a taint tracking configuration for reasoning about bypass of sensitive action guards.
 */
import javascript
private import semmle.javascript.flow.Tracking
private import semmle.javascript.security.SensitiveActions

/**
 * A data flow source for bypass of sensitive action guards.
 */
abstract class ConditionalBypassSource extends DataFlow::Node { }

/**
 * A data flow sink for bypass of sensitive action guards.
 */
abstract class ConditionalBypassSink extends DataFlow::Node {

  /**
   * Gets the guarded sensitive action.
   */
  abstract SensitiveAction getAction();

}

/**
 * A sanitizer for bypass of sensitive action guards.
 */
abstract class ConditionalBypassSanitizer extends DataFlow::Node { }

/**
 * A taint tracking configuration for bypass of sensitive action guards.
 */
class ConditionalBypassDataFlowConfiguration extends TaintTracking::Configuration {
  ConditionalBypassDataFlowConfiguration() {
    this = "ConditionalBypassDataFlowConfiguration"
  }

  override
  predicate isSource(DataFlow::Node source) {
    source instanceof ConditionalBypassSource or
    source instanceof RemoteFlowSource
  }

  override
  predicate isSink(DataFlow::Node sink) {
    sink instanceof ConditionalBypassSink
  }

  override
  predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof ConditionalBypassSanitizer
  }
}


/**
 * A conditional that guards a sensitive action, e.g. `ok` in `if (ok) login()`.
 */
class SensitiveActionGuardConditional extends ConditionalBypassSink {

  SensitiveAction action;

  SensitiveActionGuardConditional() {
    exists (GuardControlFlowNode guard |
      this.asExpr() = guard.getTest() and
      guard.getBasicBlock().(ReachableBasicBlock).dominates(action.getBasicBlock())
    )
  }

  override SensitiveAction getAction() {
    result = action
  }

}
