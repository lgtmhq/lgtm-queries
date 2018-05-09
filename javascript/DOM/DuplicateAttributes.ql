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
 * @name Duplicate HTML element attributes
 * @description Specifying the same attribute twice on the same HTML element is
 *              redundant and may indicate a copy-paste mistake.
 * @kind problem
 * @problem.severity warning
 * @id js/duplicate-html-attribute
 * @tags maintainability
 *       readability
 * @precision very-high
 */

import javascript

/**
 * Holds if `earlier` and `later` are attribute definitions with the same name
 * and the same value, where `earlier` appears textually before `later`.
 */
predicate duplicate(DOM::AttributeDefinition earlier, DOM::AttributeDefinition later) {
  exists (DOM::ElementDefinition elt, int i, int j |
    earlier = elt.getAttribute(i) and later = elt.getAttribute(j) |
    i < j and
    earlier.getName() = later.getName() and
    earlier.getStringValue() = later.getStringValue()
  )
}

from DOM::AttributeDefinition earlier, DOM::AttributeDefinition later
where duplicate(earlier, later) and not duplicate(_, earlier)
select earlier, "This attribute is duplicated $@.", later, "here"
