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
 * Provides a taint-tracking configuration for reasoning about code injection.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources
import DOM
import semmle.javascript.frameworks.jQuery


/**
 * A data flow source for code injection vulnerabilities.
 */
abstract class CodeInjectionSource extends DataFlowNode { }

/**
 * A data flow sink for code injection vulnerabilities.
 */
abstract class CodeInjectionSink extends DataFlowNode { }

/**
 * A sanitizer for CodeInjection vulnerabilities.
 */
abstract class CodeInjectionSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about CodeInjection.
 */
class CodeInjectionDataFlowConfiguration extends TaintTracking::Configuration {
  CodeInjectionDataFlowConfiguration() { this = "CodeInjectionDataFlowConfiguration" }

  override predicate isSource(DataFlowNode source) {
    source instanceof CodeInjectionSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof CodeInjectionSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    node instanceof CodeInjectionSanitizer
  }

  override predicate isAdditionalTaintStep(DataFlowNode src, DataFlowNode trg) {
    super.isAdditionalTaintStep(src, trg)
    or
    // HTML sanitizers are insufficient protection against code injection
    exists(CallExpr htmlSanitizer, string calleeName |
      calleeName = htmlSanitizer.getCalleeName() and
      calleeName.regexpMatch("(?i).*html.*") and
      calleeName.regexpMatch("(?i).*(saniti[sz]|escape|strip).*") and
      trg = htmlSanitizer and src = htmlSanitizer.getArgument(0)
    )
  }
}

/**
 * An access to a property that may hold (parts of) the document URL.
 */
class LocationSource extends CodeInjectionSource {
  LocationSource() {
    isDocumentURL(this)
  }
}

/**
 * An expression which may be interpreted as an AngularJS expression.
 */
class AngularJSExpressionSink extends CodeInjectionSink {
  AngularJSExpressionSink() {
    // AngularJS expression arguments
    exists(MethodCallExpr mce, string methodName |
      this = mce.getArgument(0) and methodName = mce.getMethodName() |
      methodName = "$watch" or
      methodName = "$watchGroup" or
      methodName = "$watchCollection" or
      methodName = "$eval" or
      methodName = "$evalAsync" or
      methodName = "$applyAsync" or
      methodName = "$compile" or
      methodName = "$parse" or
      methodName = "$interpolate"
    )
  }
}

/**
 * An expression which may be evaluated as JavaScript.
 */
class EvalJavaScriptSink extends CodeInjectionSink {
  EvalJavaScriptSink() {
    exists(InvokeExpr c, string callName, int index |
      callName = c.getCalleeName() and this = c.getArgument(index) |
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

/**
 * An expression which may be interpreted as a jQuery selector.
 */
class JQuerySelectorSink extends CodeInjectionSink {
  JQuerySelectorSink () {
    exists(JQueryMethodCall call, string name |
      name = call.getMethodName() and this = call.getArgument(0) |
      name = "$" or name = "jQuery"
    )
  }
}