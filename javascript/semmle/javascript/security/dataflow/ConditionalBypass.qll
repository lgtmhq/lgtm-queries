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
private import semmle.javascript.security.SensitiveActions

module ConditionalBypass {
  /**
   * A data flow source for bypass of sensitive action guards.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for bypass of sensitive action guards.
   */
  abstract class Sink extends DataFlow::Node {
    /**
     * Gets the guarded sensitive action.
     */
    abstract SensitiveAction getAction();

  }

  /**
   * A sanitizer for bypass of sensitive action guards.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint tracking configuration for bypass of sensitive action guards.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() {
      this = "ConditionalBypass" and
      exists(Source s) and exists(Sink s)
    }

    override
    predicate isSource(DataFlow::Node source) {
      source instanceof Source
    }

    override
    predicate isSink(DataFlow::Node sink) {
      sink instanceof Sink
    }

    override
    predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      node instanceof Sanitizer
    }
  }

  /**
   * A source of remote user input, considered as a flow source for bypass of
   * sensitive action guards.
   */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * Holds if `bb` dominates the basic block in which `action` occurs.
   */
  private predicate dominatesSensitiveAction(ReachableBasicBlock bb, SensitiveAction action) {
    bb = action.getBasicBlock()
    or
    exists (ReachableBasicBlock mid |
      dominatesSensitiveAction(mid, action) and
      bb = mid.getImmediateDominator()
    )
  }

  /**
   * A conditional that guards a sensitive action, e.g. `ok` in `if (ok) login()`.
   */
  class SensitiveActionGuardConditional extends Sink {

    SensitiveAction action;

    SensitiveActionGuardConditional() {
      exists (GuardControlFlowNode guard |
        this.asExpr() = guard.getTest() and
        dominatesSensitiveAction(guard.getBasicBlock(), action)
      )
    }

    override SensitiveAction getAction() {
      result = action
    }

  }
}

/** DEPRECATED: Use `ConditionalBypass::Source` instead. */
deprecated class ConditionalBypassSource = ConditionalBypass::Source;

/** DEPRECATED: Use `ConditionalBypass::Sink` instead. */
deprecated class ConditionalBypassSink = ConditionalBypass::Sink;

/** DEPRECATED: Use `ConditionalBypass::Sanitizer` instead. */
deprecated class ConditionalBypassSanitizer = ConditionalBypass::Sanitizer;

/** DEPRECATED: Use `ConditionalBypass::Configuration` instead. */
deprecated class ConditionalBypassDataFlowConfiguration = ConditionalBypass::Configuration;
