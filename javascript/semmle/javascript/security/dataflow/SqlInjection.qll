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
 * Provides a taint tracking configuration for reasoning about SQL injection
 * vulnerabilities.
 */

import javascript

/**
 * A data flow source for SQL-injection vulnerabilities.
 */
abstract class SqlInjectionSource extends DataFlowNode { }

/**
 * A data flow sink for SQL-injection vulnerabilities.
 */
abstract class SqlInjectionSink extends DataFlowNode { }

/**
 * A sanitizer for SQL-injection vulnerabilities.
 */
abstract class SqlInjectionSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about SQL-injection vulnerabilities.
 */
class SqlInjectionTrackingConfig extends TaintTracking::Configuration {
  SqlInjectionTrackingConfig() {
    this = "SqlInjection"
  }

  override predicate isSource(DataFlowNode source) {
    source instanceof SqlInjectionSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof SqlInjectionSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    node instanceof SqlInjectionSanitizer
  }
}

/** An SQL expression passed to an API call that executes SQL. */
class SqlInjectionExprSink extends SqlInjectionSink {
  SqlInjectionExprSink() {
    this instanceof SQL::SqlString
  }
}

/** An expression that sanitizes a value for the purposes of SQL injection. */
class SqlInjectionSanitizerExpr extends SqlInjectionSanitizer {
  SqlInjectionSanitizerExpr() {
    this = any(SQL::SqlSanitizer ss).getOutput()
  }
}
