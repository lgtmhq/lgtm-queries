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
private predicate hasSanitizingSubstring(DataFlow::Node nd) {
  exists (Expr e | e = nd.asExpr() |
    (e instanceof AddExpr or e instanceof AssignAddExpr) and
    hasSanitizingSubstring(DataFlow::valueNode(e.getAChildExpr()))
    or
    e.getStringValue().regexpMatch(".*[?#].*")
  )
  or
  nd.isIncomplete(_)
  or
  hasSanitizingSubstring(nd.getAPredecessor())
}

/**
 * Holds if data that flows from `source` to `sink` may have a string
 * containing the character `?` or `#` prepended to it.
 *
 * This is considered as a sanitizing edge for the URL redirection queries.
 */
predicate sanitizingPrefixEdge(DataFlow::Node source, DataFlow::Node sink) {
  exists (AddExpr add, DataFlow::Node left |
    source.asExpr() = add.getRightOperand() and
    sink.asExpr() = add and
    left.asExpr() = add.getLeftOperand() and
    hasSanitizingSubstring(left)
  )
  or
  exists (TemplateLiteral tl, int i, DataFlow::Node elt |
    source.asExpr() = tl.getElement(i) and
    sink.asExpr() = tl and
    elt.asExpr() = tl.getElement([0..i-1]) and
    hasSanitizingSubstring(elt)
  )
}
