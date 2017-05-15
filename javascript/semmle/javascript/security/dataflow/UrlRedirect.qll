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
 * Provides a taint-tracking configuration for reasoning about unvalidated URL
 * redirection problems.
 */

import javascript
import RemoteFlowSources

/**
 * A data flow source for unvalidated URL redirect vulnerabilities.
 */
abstract class UrlRedirectSource extends DataFlowNode { }

/**
 * A data flow sink for unvalidated URL redirect vulnerabilities.
 */
abstract class UrlRedirectSink extends DataFlowNode {
  UrlRedirectSink() {
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
abstract class UrlRedirectSanitizer extends DataFlowNode { }

/**
 * A taint-tracking configuration for reasoning about unvalidated URL redirections.
 */
class UrlRedirectDataFlowConfiguration extends TaintTrackingConfiguration {
  UrlRedirectDataFlowConfiguration() { this = "UrlRedirectDataFlowConfiguration" }

  override predicate isValidFlowSource(DataFlowNode source) {
    source instanceof UrlRedirectSource or
    source instanceof RemoteFlowSource
  }

  override predicate isValidFlowSink(DataFlowNode sink) {
    sink instanceof UrlRedirectSink
  }

  override predicate isProhibitedFlowNode(DataFlowNode node) {
    node instanceof UrlRedirectSanitizer
  }
}

/**
 * An HTTP redirect, considered as a sink for `UrlRedirectDataFlowConfiguration`.
 */
class RedirectSink extends UrlRedirectSink {
  RedirectSink() {
    this = any(HTTP::RedirectInvocation redir).getUrlArgument()
  }
}

/**
 * A definition of the HTTP "Location" header, considered as a sink for
 * `UrlRedirectDataFlowConfiguration`.
 */
class LocationHeaderSink extends UrlRedirectSink {
  LocationHeaderSink() {
    any(HTTP::HeaderDefinition def).defines("Location", this)
  }
}

/**
 * Gets a string literal that may flow into `nd` or one of its operands,
 * assuming that it is a concatenation.
 */
private StringLiteral getASubstring(DataFlowNode nd) {
  exists (DataFlowNode src | src = nd.getALocalSource() |
    (src instanceof AddExpr or src instanceof AssignAddExpr) and
    result = getASubstring(src.(Expr).getAChildExpr())
    or
    result = src
  )
}

/**
 * A string concatenation containing the character `?` or `#`,
 * considered as a sanitizer for `UrlRedirectDataFlowConfiguration`.
 */
class ConcatenationSanitizer extends UrlRedirectSanitizer {
  ConcatenationSanitizer() {
    exists (StringLiteral prefix |
      prefix = getASubstring(this.(AddExpr).getLeftOperand()) and
      prefix.getStringValue().regexpMatch(".*[?#].*")
    )
  }
}

/**
 * A variable use that is guarded by an expression that
 * sanitizes this variable for the purposes of URL redirection.
 */
class GuardSanitizer extends UrlRedirectSanitizer {
  GuardSanitizer() {
    exists (SsaVariable v | this = v.getAUse() |
      // either `v` is a refined variable where the guard performs
      // sanitization
      exists (SsaRefinementNode ref | v = ref.getVariable() |
        guardSanitizes(ref.getGuard(), _)
      )
      or
      // or there is a non-refining guard that dominates this use
      exists (ConditionGuardNode guard |
        guardSanitizes(guard, v) and guard.dominates(this.(VarUse).getBasicBlock())
      )
    )
  }
}

/**
 * Holds if `e` sanitizes `v` for the purposes of URL redirection, provided
 * it evaluates to `outcome`.
 */
private predicate sanitizes(Expr e, boolean outcome, SsaVariable v) {
  // `isLocalUrl(v)` sanitizes `v` if it evaluates to `true`
  exists (CallExpr isLocalUrl | e = isLocalUrl |
    isLocalUrl.getCalleeName().regexpMatch("(?i)(is_?)?local_?url") and
    isLocalUrl.getAnArgument() = v.getAUse() and
    outcome = true
  )
  or
  // `v === "foo"` sanitizes `v` if it evaluates to `true`, `v !== "bar"`
  // if it evaluates to `false`
  exists (EqualityTest eql | e = eql |
    eql.hasOperands(v.getAUse(), any(Expr c | exists(c.getStringValue()))) and
    outcome = eql.getPolarity()
  )
}

/**
 * Holds if `guard` is sanitizes `v` for the purposes of URL redirection.
 */
private predicate guardSanitizes(ConditionGuardNode guard, SsaVariable v) {
  sanitizes(guard.getTest(), guard.getOutcome(), v)
}