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
 * Provides a taint-tracking configuration for reasoning about DOM-based
 * cross-site scripting vulnerabilities.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources
import semmle.javascript.frameworks.jQuery

/**
 * A data flow source for XSS vulnerabilities.
 */
abstract class XssSource extends DataFlow::Node { }

/**
 * A data flow sink for XSS vulnerabilities.
 */
abstract class XssSink extends DataFlow::Node { }

class DefaultSink extends XssSink {
  DefaultSink() {
    this instanceof DomSink or
    this instanceof LibrarySink
  }
}

/**
 * A sanitizer for XSS vulnerabilities.
 */
abstract class XssSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about XSS.
 */
class XssDataFlowConfiguration extends TaintTracking::Configuration {
  XssDataFlowConfiguration() { this = "XssDataFlowConfiguration" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof XssSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof XssSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    isSafeLocationProperty(node.asExpr()) or
    node instanceof XssSanitizer
  }
}

/**
 * An access of the URL of this page, or of the referrer to this page.
 */
class LocationSource extends XssSource, DataFlow::ValueNode {
  LocationSource() {
    isDocumentURL(astNode)
  }
}

/**
 * An expression whose value is interpreted as HTML or CSS
 * and may be inserted into the DOM through a library.
 */
class LibrarySink extends XssSink {
  LibrarySink() {
    // Call to a jQuery method that inserts its argument into the DOM
    exists(JQueryMethodCall call |
      call.interpretsArgumentsAsHtml() and
      this.asExpr() = call.getAnArgument()
    ) or
    any(AngularJS::AngularJSCall call).interpretsArgumentAsHtml(this.asExpr())
  }
}

/**
 * An expression whose value is interpreted as HTML or CSS
 * and may be inserted into the DOM.
 */
class DomSink extends XssSink {
  DomSink() {
    // Call to a DOM function that inserts its argument into the DOM
    any(DomMethodCallExpr call).interpretsArgumentsAsHTML(this.asExpr())
    or
    // Assignment to a dangerous DOM property
    exists (DomPropWriteNode pw |
      pw.interpretsValueAsHTML() and
      this = DataFlow::valueNode(pw.getRhs())
    )
  }
}

/**
 * An expression whose value is interpreted as HTML by a DOMParser.
 */
class DomParserSink extends XssSink {
  DomParserSink() {
    exists (DataFlow::GlobalVarRefNode domParser |
      domParser.getName() = "DOMParser" and
      this = domParser.getAnInstantiation().getAMethodCall("parseFromString").getArgument(0)
    )
  }
}

/**
 * A React `dangerouslySetInnerHTML` attribute, viewed as an XSS sink.
 *
 * Any write to the `__html` property of an object assigned to this attribute
 * is considered an XSS sink.
 */
class DangerouslySetInnerHtmlSink extends XssSink, DataFlow::ValueNode {
  DangerouslySetInnerHtmlSink() {
    exists (JSXAttribute attr, DataFlow::SourceNode valueSrc, PropWriteNode pwn |
      attr.getName() = "dangerouslySetInnerHTML" and
      valueSrc.flowsToExpr(attr.getValue()) and
      valueSrc.flowsToExpr(pwn.getBase()) and
      pwn.getPropertyName() = "__html" and
      astNode = pwn.getRhs()
    )
  }
}
