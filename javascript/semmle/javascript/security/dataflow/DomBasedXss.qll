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

module DomBasedXss {
  /**
   * A data flow source for XSS vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for XSS vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node { }

  class DefaultSink extends Sink {
    DefaultSink() {
      this instanceof DomSink or
      this instanceof LibrarySink
    }
  }

  /**
   * A sanitizer for XSS vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * A taint-tracking configuration for reasoning about XSS.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() { 
      this = "DomBasedXss" and
      exists(Source s) and exists(Sink s)
    }

    override predicate isSource(DataFlow::Node source) {
      source instanceof Source
    }

    override predicate isSink(DataFlow::Node sink) {
      sink instanceof Sink
    }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      isSafeLocationProperty(node.asExpr()) or
      node instanceof Sanitizer
    }
  }

  /** A source of remote user input, considered as a flow source for DOM-based XSS. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * An access of the URL of this page, or of the referrer to this page.
   */
  class LocationSource extends Source, DataFlow::ValueNode {
    LocationSource() {
      isDocumentURL(astNode)
    }
  }

  /**
   * An expression whose value is interpreted as HTML or CSS
   * and may be inserted into the DOM through a library.
   */
  class LibrarySink extends Sink {
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
  class DomSink extends Sink {
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
  class DomParserSink extends Sink {
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
  class DangerouslySetInnerHtmlSink extends Sink, DataFlow::ValueNode {
    DangerouslySetInnerHtmlSink() {
      exists (DataFlow::Node danger, DataFlow::SourceNode valueSrc |
        exists (JSXAttribute attr |
          attr.getName() = "dangerouslySetInnerHTML" and
          attr.getValue() = danger.asExpr()
        )
        or
        exists (ReactElementDefinition def, DataFlow::ObjectExprNode props |
          props.flowsTo(def.getProps()) and
          props.hasPropertyWrite("dangerouslySetInnerHTML", danger)
        ) |
        valueSrc.flowsTo(danger) and
        valueSrc.hasPropertyWrite("__html", this)
      )
    }
  }

}

/** DEPRECATED: Use `DomBasedXss::Source` instead. */
deprecated class XssSource = DomBasedXss::Source;

/** DEPRECATED: Use `DomBasedXss::Sink` instead. */
deprecated class XssSink = DomBasedXss::Sink;

/** DEPRECATED: Use `DomBasedXss::Sanitizer` instead. */
deprecated class XssSanitizer = DomBasedXss::Sanitizer;

/** DEPRECATED: Use `DomBasedXss::Configuration` instead. */
deprecated class XssDataFlowConfiguration = DomBasedXss::Configuration;
