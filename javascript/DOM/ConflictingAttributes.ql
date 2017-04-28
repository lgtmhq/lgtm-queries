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
 * @name Conflicting HTML element attributes
 * @description If an HTML element has two attributes with the same name
 *              but different values, its behavior may be browser-dependent.
 * @kind problem
 * @problem.severity error
 * @tags maintainability
 *       correctness
 *       external/cwe/cwe-758
 * @precision very-high
 */

import DOM.DOM

/**
 * Holds if `earlier` and `later` are attribute definitions with the same name
 * and different values, where `earlier` appears textually before `later`.
 */
predicate conflict(DOMAttributeDefinition earlier, DOMAttributeDefinition later) {
  exists (DOMElementDefinition elt, int i, int j |
    earlier = elt.getAttribute(i) and later = elt.getAttribute(j) |
    i < j and
    earlier.getName() = later.getName() and
    not earlier.getStringValue() = later.getStringValue()
  )
}

from DOMAttributeDefinition earlier, DOMAttributeDefinition later
where conflict(earlier, later) and not conflict(_, earlier)
select earlier, "This attribute has the same name as $@ of the same element, " +
       "but a different value.", later, "another attribute"