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
 * Provides a taint-tracking configuration for reasoning about cross-site
 * scripting vulnerabilities.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources
import semmle.javascript.frameworks.jQuery

/*
 * Many sources and sinks taken from
 *
 * https://github.com/wisec/domxsswiki/wiki
 */

/**
 * Holds if `name` is a jQuery method that interprets its arguments as HTML
 * or CSS.
 */
predicate jqueryXss(string name) {
  name = "addClass" or
  name = "after" or
  name = "append" or
  name = "appendTo" or
  name = "before" or
  name = "html" or
  name = "insertAfter" or
  name = "insertBefore" or
  name = "parseHTML" or
  name = "prepend" or
  name = "prependTo" or
  name = "prop" or
  name = "replaceWith" or
  name = "wrap" or
  name = "wrapAll" or
  name = "wrapInner"
}

/**
 * Holds if `sink` is an expression whose value is interpreted as HTML or CSS
 * and may be inserted into the DOM.
 */
private predicate isSink(Expr sink) {
  // Call to a DOM function that inserts its argument into the DOM
  exists (MethodCallExpr mce, string methodName, int index |
    isDomValue(mce.getReceiver()) and methodName = mce.getMethodName() and
    sink = mce.getArgument(index) |
    methodName = "write" or
    methodName = "writeln" or
    methodName = "insertAdjacentHTML" and index = 0 or
    methodName = "insertAdjacentElement" and index = 0 or
    methodName = "insertBefore" and index = 0 or
    methodName = "createElement" and index = 0 or
    methodName = "appendChild" and index = 0 or
    methodName = "setAttribute" and index = 0
  )
  or
  // Assignment to a dangerous DOM property
  exists (PropWriteNode pw |
    isDomValue(pw.getBase()) and sink = pw.getRhs() |
    pw.getPropertyName() = "innerHTML" or
    pw.getPropertyName() = "outerHTML"
  )
  or
  // Call to a jQuery method that inserts its argument into the DOM
  exists(JQueryMethodCall call |
    jqueryXss(call.getMethodName()) and
    sink = call.getAnArgument()
  )
}

/**
 * A data flow source for XSS vulnerabilities.
 */
abstract class XssSource extends DataFlowNode { }

/**
 * A data flow sink for XSS vulnerabilities.
 */
abstract class XssSink extends DataFlowNode { }

class DefaultSink extends XssSink {
  DefaultSink() { isSink(this) }
}

/**
 * A sanitizer for XSS vulnerabilities.
 */
abstract class XssSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about XSS.
 */
class XssDataFlowConfiguration extends TaintTracking::Configuration {
  XssDataFlowConfiguration() { this = "XssDataFlowConfiguration" }

  override predicate isSource(DataFlowNode source) {
    source instanceof XssSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof XssSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    isSafeLocationProperty(node) or
    node instanceof XssSanitizer
  }
}

/**
 * An access of the URL of this page, or of the referrer to this page.
 */
class LocationSource extends XssSource {
  LocationSource() {
    isDocumentURL(this)
  }
}

/**
 * A React `dangerouslySetInnerHTML` attribute, viewed as an XSS sink.
 */
class DangerouslySetInnerHtmlSink extends XssSink {
  DangerouslySetInnerHtmlSink() {
    exists (JSXAttribute attr |
      attr.getName() = "dangerouslySetInnerHTML" and
      this = attr.getValue()
    )
  }
}
