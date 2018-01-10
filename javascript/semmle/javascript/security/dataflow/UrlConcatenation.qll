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
 * Provides a class for detecting string concatenations involving
 * the characters `?` and `#`, which are considered sanitizers for
 * the URL redirection queries.
 */

import javascript

/**
 * Holds if a string value containing `?` or `#` may flow into
 * `nd` or one of its operands, assuming that it is a concatenation.
 */
private predicate hasSanitizingSubstring(DataFlowNode nd) {
  exists (DataFlowNode src | src = nd.getALocalSource() |
    (src instanceof AddExpr or src instanceof AssignAddExpr) and
    hasSanitizingSubstring(src.(Expr).getAChildExpr())
    or
    src.(Expr).getStringValue().regexpMatch(".*[?#].*")
  )
}

/**
 * Holds if a string value containing `?` or `#` may precede
 * `nd` in a string concatenation.
 */
private predicate hasSanitizingPrefix(DataFlowNode nd) {
  exists (AddExpr add | nd = add.getRightOperand() |
    hasSanitizingSubstring(add.getLeftOperand())
  ) or
  exists (ParExpr pe | nd = pe.getExpression() |
    hasSanitizingPrefix(pe)
  ) or
  exists (TemplateLiteral tl, int i | nd = tl.getElement(i) |
    hasSanitizingSubstring(tl.getElement([0..i-1]))
  )
}

/**
 * An expression to which a string containing the character `?` or `#`
 * is prepended.
 *
 * This is considered as a sanitizer for the URL redirection queries.
 */
class UrlQueryStringConcat extends Expr {
  UrlQueryStringConcat() {
    hasSanitizingPrefix(this)
  }
}