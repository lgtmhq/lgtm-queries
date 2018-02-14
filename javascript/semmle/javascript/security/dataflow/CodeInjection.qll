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
 * Provides a taint-tracking configuration for reasoning about code injection.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources

/**
 * A data flow source for code injection vulnerabilities.
 */
abstract class CodeInjectionSource extends DataFlow::Node { }

/**
 * A data flow sink for code injection vulnerabilities.
 */
abstract class CodeInjectionSink extends DataFlow::Node { }

/**
 * A sanitizer for CodeInjection vulnerabilities.
 */
abstract class CodeInjectionSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about CodeInjection.
 */
class CodeInjectionDataFlowConfiguration extends TaintTracking::Configuration {
  CodeInjectionDataFlowConfiguration() { this = "CodeInjectionDataFlowConfiguration" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof CodeInjectionSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof CodeInjectionSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    isSafeLocationProperty(node.asExpr()) or
    node instanceof CodeInjectionSanitizer
  }

  override predicate isAdditionalTaintStep(DataFlow::Node src, DataFlow::Node trg) {
    super.isAdditionalTaintStep(src, trg)
    or
    // HTML sanitizers are insufficient protection against code injection
    exists(CallExpr htmlSanitizer, string calleeName |
      calleeName = htmlSanitizer.getCalleeName() and
      calleeName.regexpMatch("(?i).*html.*") and
      calleeName.regexpMatch("(?i).*(saniti[sz]|escape|strip).*") and
      trg.asExpr() = htmlSanitizer and src.asExpr() = htmlSanitizer.getArgument(0)
    )
  }
}

/**
 * An access to a property that may hold (parts of) the document URL.
 */
class LocationSource extends CodeInjectionSource, DataFlow::ValueNode {
  LocationSource() {
    isDocumentURL(astNode)
  }
}

/**
 * An expression which may be interpreted as an AngularJS expression.
 */
class AngularJSExpressionSink extends CodeInjectionSink, DataFlow::ValueNode {
  AngularJSExpressionSink() {
    any(AngularJS::AngularJSCall call).interpretsArgumentAsCode(this.asExpr())
  }
}

/**
 * An expression which may be evaluated as JavaScript.
 */
class EvalJavaScriptSink extends CodeInjectionSink, DataFlow::ValueNode {
  EvalJavaScriptSink() {
    exists(InvokeExpr c, string callName, int index |
      callName = c.getCalleeName() and astNode = c.getArgument(index) |
      callName = "eval" and index = 0 or
      callName = "Function" or
      callName = "execScript" and index = 0 or
      callName = "executeJavaScript" and index = 0 or
      callName = "execCommand" and index = 0 or
      callName = "setTimeout" and index = 0 or
      callName = "setInterval" and index = 0 or
      callName = "setImmediate" and index = 0
    )
  }
}
