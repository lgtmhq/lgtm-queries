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
 * Provides a taint tracking configuration for reasoning about NoSQL injection
 * vulnerabilities.
 */

import javascript

/**
 * A data flow source for NoSQL-injection vulnerabilities.
 */
abstract class NosqlInjectionSource extends DataFlowNode { }

/**
 * A data flow sink for SQL-injection vulnerabilities.
 */
abstract class NosqlInjectionSink extends DataFlowNode { }

/**
 * A sanitizer for SQL-injection vulnerabilities.
 */
abstract class NosqlInjectionSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about SQL-injection vulnerabilities.
 */
class NosqlInjectionTrackingConfig extends TaintTracking::Configuration {
  NosqlInjectionTrackingConfig() {
    this = "NosqlInjection"
  }

  override predicate isSource(DataFlowNode source) {
    source instanceof NosqlInjectionSource or
    source instanceof Express::RequestBodyAccess
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof NosqlInjectionSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    node instanceof NosqlInjectionSanitizer
  }
}

/**
 * A taint tracking configuration for tracking user input that flows
 * into a call to `JSON.parse`.
 */
private class RemoteJsonTrackingConfig extends TaintTracking::Configuration {
  RemoteJsonTrackingConfig() {
    this = "RemoteJsonTrackingConfig"
  }

  override predicate isSource(DataFlowNode nd) {
    nd instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode nd) {
    nd = any(JsonParseCall c).getArgument(0)
  }
}

/**
 * A call to `JSON.parse` where the argument is user-provided.
 */
class RemoteJson extends NosqlInjectionSource {
  RemoteJson() {
    any(RemoteJsonTrackingConfig cfg).flowsFrom(this.(JsonParseCall).getArgument(0), _)
  }
}

/** An expression interpreted as a NoSQL query, viewed as a sink. */
class NosqlQuerySink extends NosqlInjectionSink {
  NosqlQuerySink() {
    this instanceof NoSQL::Query
  }
}

/**
 * An additional flow step to track taint through NoSQL query objects.
 */
class NosqlQueryFlowTarget extends TaintTracking::FlowTarget {
  NoSQL::Query query;
  PropWriteNode pwn;

  NosqlQueryFlowTarget() {
    exists (DataFlowNode queryObj | queryObj = query.getALocalSource() |
      this.getALocalSource() = queryObj and
      queryObj = pwn.getBase().getALocalSource()
    )
  }

  override DataFlowNode getATaintSource() {
    result = pwn.getRhs()
  }
}
