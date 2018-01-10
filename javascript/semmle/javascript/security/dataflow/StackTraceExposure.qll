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
 * Provides a taint-tracking configuration for reasoning about stack trace
 * exposure problems.
 */

import javascript

/**
 * A data flow source for stack trace exposure vulnerabilities.
 */
abstract class StackTraceExposureSource extends DataFlowNode { }

/**
 * A data flow sink for stack trace exposure vulnerabilities.
 */
abstract class StackTraceExposureSink extends DataFlowNode { }

class StackTraceExposureTrackingConfig extends TaintTracking::Configuration {
  StackTraceExposureTrackingConfig() {
    this = "StackTraceExposureTrackingConfig"
  }

  override predicate isSource(DataFlowNode src) {
    src instanceof StackTraceExposureSource
  }

  predicate isSink(DataFlowNode snk) {
    snk instanceof StackTraceExposureSink
  }
}

/**
 * A read of the `stack` property of an exception, viewed as a data flow
 * sink for stack trace exposure vulnerabilities.
 */
class DefaultStackTraceExposureSource extends StackTraceExposureSource {
  DefaultStackTraceExposureSource() {
    // any read of the `stack` property of an exception is a source
    exists (TryStmt try, PropReadNode pr | pr = this |
      pr.getBase() = try.getACatchClause().getParameterVariable(_).getAnAccess() and
      pr.getPropertyName() = "stack"
    )
  }
}

/**
 * An expression that can become part of an HTTP response body, viewed
 * as a data flow sink for stack trace exposure vulnerabilities.
 */
class DefaultStackTraceExposureSink extends StackTraceExposureSink {
  DefaultStackTraceExposureSink() {
    this instanceof HTTP::ResponseBody
  }
}
