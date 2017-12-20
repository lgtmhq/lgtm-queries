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
 * A data flow source for XSS vulnerabilities.
 */
abstract class XssSource extends DataFlowNode { }

/**
 * A data flow sink for XSS vulnerabilities.
 */
abstract class XssSink extends DataFlowNode { }

class DefaultSink extends XssSink {
  DefaultSink() {
    this instanceof DomSink or
    this instanceof LibrarySink
  }
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
    super.isSanitizer(node) or
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
 * An expression whose value is interpreted as HTML or CSS
 * and may be inserted into the DOM through a library.
 */
class LibrarySink extends XssSink {
  LibrarySink() {
    // Call to a jQuery method that inserts its argument into the DOM
    exists(JQueryMethodCall call |
      call.interpretsArgumentsAsHtml() and
      this = call.getAnArgument()
    ) or
    any(AngularJS::AngularJSCall call).interpretsArgumentAsHtml(this)
  }
}

/**
 * An expression whose value is interpreted as HTML or CSS
 * and may be inserted into the DOM.
 */
class DomSink extends XssSink {
  DomSink() {
    // Call to a DOM function that inserts its argument into the DOM
    any(DomMethodCallExpr call).interpretsArgumentsAsHTML(this)
    or
    // Assignment to a dangerous DOM property
    exists (DomPropWriteNode pw |
      pw.interpretsValueAsHTML() and
      this = pw.getRhs()
    )
  }
}


/**
 * A React `dangerouslySetInnerHTML` attribute, viewed as an XSS sink.
 *
 * Any write to the `__html` property of an object assigned to this attribute
 * is considered an XSS sink.
 */
class DangerouslySetInnerHtmlSink extends XssSink {
  DangerouslySetInnerHtmlSink() {
    exists (JSXAttribute attr, DataFlowNode valueSrc, PropWriteNode pwn |
      attr.getName() = "dangerouslySetInnerHTML" and
      valueSrc = attr.getValue().(DataFlowNode).getALocalSource() and
      pwn.getBase().getALocalSource() = valueSrc and
      pwn.getPropertyName() = "__html" and
      this = pwn.getRhs()
    )
  }
}

/**
 * A conditional checking a tainted string against a regular expression, which is
 * considered to be a sanitizer.
 */
class SanitizingRegExpTest extends TaintTracking::SanitizingGuard, Expr {
  VarUse u;

  SanitizingRegExpTest() {
    exists (MethodCallExpr mce, DataFlowNode base, string m, DataFlowNode firstArg |
      mce = this and mce.calls(base, m) and firstArg = mce.getArgument(0) |
      // /re/.test(u) or /re/.exec(u)
      base.getALocalSource() instanceof RegExpLiteral and
      (m = "test" or m = "exec") and
      firstArg = u
      or
      // u.match(/re/) or u.match("re")
      base = u and
      m = "match" and
      (
       firstArg.getALocalSource() instanceof RegExpLiteral or
       firstArg.getALocalSource() instanceof ConstantString
      )
    )
    or
    // m = /re/.exec(u) and similar
    this.(AssignExpr).getRhs().(SanitizingRegExpTest).getSanitizedVarUse() = u
  }

  VarUse getSanitizedVarUse() {
    result = u
  }

  override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
    cfg instanceof XssDataFlowConfiguration and
    (outcome = true or outcome = false) and
    u = v.getAUse()
  }
}
