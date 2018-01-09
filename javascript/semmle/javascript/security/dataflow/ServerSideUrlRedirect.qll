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
 * redirection problems on the server side.
 */

import javascript
import RemoteFlowSources
import UrlConcatenation

/**
 * A data flow source for unvalidated URL redirect vulnerabilities.
 */
abstract class ServerSideUrlRedirectSource extends DataFlowNode { }

/**
 * A data flow sink for unvalidated URL redirect vulnerabilities.
 */
abstract class ServerSideUrlRedirectSink extends DataFlowNode {
  ServerSideUrlRedirectSink() {
    // it's only a sink if we cannot prove that this is a local redirect
    exists (DataFlowNode prefix | prefix = getAPrefix(this) |
      not exists(prefix.(Expr).getStringValue())
      or
      exists (string prefixVal | prefixVal = prefix.(Expr).getStringValue() |
        // local URLs (i.e., URLs that start with `/` not followed by `\` or `/`,
        // or that start with `~/`) are unproblematic
        not prefixVal.regexpMatch("/[^\\\\/].*|~/.*") and
        // so are localhost URLs
        not prefixVal.regexpMatch("(\\w+:)?//localhost[:/].*")
      )
    )
  }
}

/**
 * Gets a data flow node that may end up being a prefix of the string
 * concatenation `nd`.
 */
private DataFlowNode getAPrefix(DataFlowNode nd) {
  exists (DataFlowNode src | src = nd.getALocalSource() |
    if (src instanceof AddExpr or src instanceof AssignAddExpr) then
      result = getAPrefix(src.(Expr).getChildExpr(0))
    else
      result = src
  )
}

/**
 * A sanitizer for unvalidated URL redirect vulnerabilities.
 */
abstract class ServerSideUrlRedirectSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about unvalidated URL redirections.
 */
class ServerSideUrlRedirectDataFlowConfiguration extends TaintTracking::Configuration {
  ServerSideUrlRedirectDataFlowConfiguration() { this = "ServerSideUrlRedirectDataFlowConfiguration" }

  override predicate isSource(DataFlowNode source) {
    source instanceof ServerSideUrlRedirectSource or
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlowNode sink) {
    sink instanceof ServerSideUrlRedirectSink
  }

  override predicate isSanitizer(DataFlowNode node) {
    super.isSanitizer(node) or
    node instanceof ServerSideUrlRedirectSanitizer
  }
}

/**
 * An HTTP redirect, considered as a sink for `ServerSideUrlRedirectDataFlowConfiguration`.
 */
class RedirectSink extends ServerSideUrlRedirectSink {
  RedirectSink() {
    this = any(HTTP::RedirectInvocation redir).getUrlArgument()
  }
}

/**
 * A definition of the HTTP "Location" header, considered as a sink for
 * `ServerSideUrlRedirectDataFlowConfiguration`.
 */
class LocationHeaderSink extends ServerSideUrlRedirectSink {
  LocationHeaderSink() {
    any(HTTP::ExplicitHeaderDefinition def).definesExplicitly("Location", this)
  }
}

/**
 * A string concatenation containing the character `?` or `#`,
 * considered as a sanitizer for `ServerSideUrlRedirectDataFlowConfiguration`.
 */
class ConcatenationSanitizer extends ServerSideUrlRedirectSanitizer {
  ConcatenationSanitizer() {
    this instanceof UrlQueryStringConcat
  }
}

/**
 * A call to a function called `isLocalUrl` or similar, which is
 * considered to sanitize a variable for purposes of URL redirection.
 */
class LocalUrlSanitizingGuard extends TaintTracking::SanitizingGuard, CallExpr {
  override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
    cfg instanceof ServerSideUrlRedirectDataFlowConfiguration and
    // `isLocalUrl(v)` sanitizes `v` if it evaluates to `true`
    this.getCalleeName().regexpMatch("(?i)(is_?)?local_?url") and
    this.getAnArgument() = v.getAUse() and
    outcome = true
  }
}

/**
 * A comparison to a constant string, which is considered to
 * sanitize a variable for purposes of URL redirection.
 */
class UrlWhitelistSanitizingGuard extends TaintTracking::SanitizingGuard, EqualityTest {
  override predicate sanitizes(TaintTracking::Configuration cfg, boolean outcome, SsaVariable v) {
    cfg instanceof ServerSideUrlRedirectDataFlowConfiguration and
    // `v === "foo"` sanitizes `v` if it evaluates to `true`, `v !== "bar"`
    // if it evaluates to `false`
    this.hasOperands(v.getAUse(), any(Expr c | exists(c.getStringValue()))) and
    outcome = this.getPolarity()
  }
}
