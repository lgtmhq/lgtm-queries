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
 * @name Ambiguous HTML id attribute
 * @description If an HTML document contains two elements with the
 *              same id attribute, it may be interpreted differently
 *              by different browsers.
 * @kind problem
 * @problem.severity error
 * @id js/duplicate-html-id
 * @tags maintainability
 *       correctness
 * @precision very-high
 */

import javascript

/**
 * Holds if `elt` defines a DOM element with the given `id`
 * under document `root` at the given `line` and `column`.
 *
 * Furthermore, the id is required to be non-empty (since empty ids
 * are reported by a different query).
 */
predicate elementAt(DOM::ElementDefinition elt, string id, DOM::ElementDefinition root,
                    int line, int column) {
  id = elt.getAttributeByName("id").getStringValue() and id != "" and
  root = elt.getRoot() and
  elt.getLocation().hasLocationInfo(_, line, column, _, _)
}

/**
 * Holds if elements `earlier` and `later` have the same id and belong
 * to the same document, and `earlier` appears textually before `later`.
 */
predicate sameId(DOM::ElementDefinition earlier, DOM::ElementDefinition later) {
  exists (string id, DOM::ElementDefinition root, int l1, int c1, int l2, int c2 |
    elementAt(earlier, id, root, l1, c1) and elementAt(later, id, root, l2, c2) |
    l1 < l2 or
    l1 = l2 and c1 < c2
  )
}

from DOM::ElementDefinition earlier, DOM::ElementDefinition later
where sameId(earlier, later) and not sameId(_, earlier)
select earlier, "This element has the same id as $@.", later, "another element"
