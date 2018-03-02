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
 * Provides a taint-tracking configuration for reasoning about reflected
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

/**
 * A sanitizer for XSS vulnerabilities.
 */
abstract class XssSanitizer extends DataFlow::Node { }

/**
 * A taint-tracking configuration for reasoning about XSS.
 */
class XssDataFlowConfiguration extends TaintTracking::Configuration {
  XssDataFlowConfiguration() { this = "ReflectedXssDataFlowConfiguration" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof XssSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof XssSink
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof XssSanitizer
  }
}

/**
 * An expression that is sent as part of an HTTP response, considered as an XSS sink.
 *
 * We exclude cases where the route handler sets either an unknown content type or
 * a content type that does not (case-insensitively) contain the string "html". This
 * is to prevent us from flagging plain-text or JSON responses as vulnerable.
 */
private class HttpResponseSink extends XssSink {
  HttpResponseSink() {
    exists (HTTP::ResponseSendArgument sendarg | sendarg = asExpr() |
      forall (HTTP::HeaderDefinition hd |
        hd = sendarg.getRouteHandler().getAResponseHeader("Content-Type") |
        exists (string tp | hd.defines("Content-Type", tp) |
          tp.toLowerCase().matches("%html%")
        )
      )
    )
  }
}
