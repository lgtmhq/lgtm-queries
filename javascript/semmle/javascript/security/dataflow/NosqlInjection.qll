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
 * Provides a taint tracking configuration for reasoning about NoSQL injection
 * vulnerabilities.
 */

import javascript

/**
 * A data flow source for NoSQL-injection vulnerabilities.
 */
abstract class NosqlInjectionSource extends DataFlow::Node { }

/**
 * A data flow sink for SQL-injection vulnerabilities.
 */
abstract class NosqlInjectionSink extends DataFlow::Node { }

/**
 * A sanitizer for SQL-injection vulnerabilities.
 */
abstract class NosqlInjectionSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about SQL-injection vulnerabilities.
 */
class NosqlInjectionTrackingConfig extends TaintTracking::Configuration {
  NosqlInjectionTrackingConfig() {
    this = "NosqlInjection"
  }

  override predicate isSource(DataFlow::Node source) {
    source instanceof NosqlInjectionSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof NosqlInjectionSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof NosqlInjectionSanitizer
  }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    // additional flow step to track taint through NoSQL query objects
    exists (NoSQL::Query query, PropWriteNode pwn, DataFlow::SourceNode queryObj |
      queryObj.flowsToExpr(query) and
      queryObj.flowsTo(succ) and
      queryObj.flowsToExpr(pwn.getBase()) and
      pred = DataFlow::valueNode(pwn.getRhs())
    )
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

  override predicate isSource(DataFlow::Node nd) {
    nd instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node nd) {
    nd.asExpr() = any(JsonParseCall c).getArgument(0)
  }
}

/**
 * A call to `JSON.parse` where the argument is user-provided.
 */
class RemoteJson extends NosqlInjectionSource, DataFlow::ValueNode {
  RemoteJson() {
    exists (DataFlow::Node parsedArg |
      parsedArg.asExpr() = astNode.(JsonParseCall).getArgument(0) and
      any(RemoteJsonTrackingConfig cfg).flowsFrom(parsedArg, _)
    )
  }
}

/** An expression interpreted as a NoSQL query, viewed as a sink. */
class NosqlQuerySink extends NosqlInjectionSink, DataFlow::ValueNode {
  override NoSQL::Query astNode;
}
