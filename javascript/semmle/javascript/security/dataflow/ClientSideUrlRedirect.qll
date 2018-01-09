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
 * Provides a taint-tracking configuration for reasoning about unvalidated URL
 * redirection problems on the client side.
 */

import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources
import UrlConcatenation

/**
 * A data flow source for unvalidated URL redirect vulnerabilities.
 */
abstract class ClientSideUrlRedirectSource extends DataFlowNode { }

/**
 * A data flow sink for unvalidated URL redirect vulnerabilities.
 */
abstract class ClientSideUrlRedirectSink extends DataFlowNode { }

/**
 * A sanitizer for unvalidated URL redirect vulnerabilities.
 */
abstract class ClientSideUrlRedirectSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about unvalidated URL redirections.
 */
class ClientSideUrlRedirectDataFlowConfiguration extends TaintTracking::Configuration {
  ClientSideUrlRedirectDataFlowConfiguration() { this = "ClientSideUrlRedirectDataFlowConfiguration" }

  override predicate isSource(DataFlowNode source) {
    source instanceof ClientSideUrlRedirectSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof ClientSideUrlRedirectSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    super.isSanitizer(node) or
    isSafeLocationProperty(node) or
    node instanceof ClientSideUrlRedirectSanitizer
  }
}

/**
 * Holds if `queryAccess` is an expression that may access the query string
 * of a URL that flows into `nd` (that is, the part after the `?`).
 */
private predicate queryAccess(DataFlowNode nd, DataFlowNode queryAccess) {
  exists (string propertyName |
    queryAccess.(PropAccess).accesses(nd, propertyName) |
    propertyName = "search" or propertyName = "hash"
  )
  or
  exists (MethodCallExpr mce, string methodName |
    mce = queryAccess and mce.calls(nd, methodName) |
    methodName = "split" and
    // exclude `location.href.split('?')[0]`, which can never refer to the query string
    not exists (PropAccess pacc | mce = pacc.getBase() | pacc.getPropertyName() = "0")
    or
    (methodName = "substring" or methodName = "substr") and
    // exclude `location.href.substring(0, ...)` and similar, which can
    // never refer to the query string
    not mce.getArgument(0).(NumberLiteral).getIntValue() = 0
  )
  or
  exists (MethodCallExpr mce |
    queryAccess = mce and
    mce.calls(any(RegExpLiteral re), "exec") and
    nd = mce.getArgument(0)
  )
}

/**
 * A taint tracking configuration for identifying accesses of the query string of the current URL.
 */
private class LocationHrefDataFlowConfiguration extends TaintTracking::Configuration {
  LocationHrefDataFlowConfiguration() {
    this = "LocationHrefDataFlowConfiguration"
  }

  override predicate isSource(DataFlowNode source) {
    isDocumentURL(source)
  }

  override predicate isSink(DataFlowNode sink) {
    queryAccess(sink, _)
  }
}

/**
 * An access of the query string of the current URL.
 */
class LocationSearchSource extends ClientSideUrlRedirectSource {
  LocationSearchSource() {
    exists(LocationHrefDataFlowConfiguration cfg, DataFlowNode nd |
      cfg.flowsFrom(nd, _) and
      queryAccess(nd, this)
    )
  }
}

/**
 * A sink which is used to set the window location.
 */
class LocationSink extends ClientSideUrlRedirectSink {
  LocationSink() {
    // A call to a `window.navigate` or `window.open`
    exists (CallExpr windowCall, string name |
      windowCall.getCallee().accessesGlobal(name) and
      this = windowCall.getArgument(0) |
      name = "navigate" or name = "open" or
      name = "openDialog" or name = "showModalDialog"
    )
    or
    // A call to `location.replace` or `location.assign`
    exists (MethodCallExpr locationCall, string name |
      isLocation(locationCall.getReceiver()) and name = locationCall.getMethodName() and
      this = locationCall.getArgument(0) |
      name = "replace" or name = "assign"
    )
    or
    // An assignment to `location`
    exists (Assignment assgn |
      isLocation(assgn.getTarget()) and this = assgn.getRhs()
    )
    or
    // An assignment to `location.href`, `location.protocol` or `location.hostname`
    exists(PropWriteNode pw, string propName |
      isLocation(pw.getBase()) and propName = pw.getPropertyName() and
      this = pw.getRhs() |
      propName = "href" or propName = "protocol" or propName = "hostname"
    )
    or
    // A redirection using the AngularJS `$location` service
    exists (AngularJS::ServiceReference service |
      service.getName() = "$location" and
      this = service.getAMethodCall("url").getArgument(0)
    )
  }
}


/**
 * A string concatenation containing the character `?` or `#`,
 * considered as a sanitizer for `ClientSideUrlRedirectDataFlowConfiguration`.
 */
class ConcatenationSanitizer extends ClientSideUrlRedirectSanitizer {
  ConcatenationSanitizer() {
    this instanceof UrlQueryStringConcat
  }
}

/**
 * An expression that may be interpreted as the URL of a script.
 */
abstract class ScriptUrlSink extends ClientSideUrlRedirectSink {
}

/**
 * An argument expression to `new Worker(...)`, viewed as
 * a `ScriptUrlSink`.
 */
class WebWorkerScriptUrlSink extends ScriptUrlSink {
  WebWorkerScriptUrlSink() {
    exists (NewExpr new |
      new.getCallee().accessesGlobal("Worker") and
      this = new.getArgument(0)
    )
  }
}

/**
 * A script or iframe `src` attribute, viewed as a `ScriptUrlSink`.
 */
class SrcAttributeUrlSink extends ScriptUrlSink {
  SrcAttributeUrlSink() {
    exists (DOM::AttributeDefinition attr, string eltName |
      attr.getElement().getName() = eltName and
      (eltName = "script" or eltName = "iframe") and
      attr.getName() = "src" and
      this = attr.getValueNode()
    )
  }
}
