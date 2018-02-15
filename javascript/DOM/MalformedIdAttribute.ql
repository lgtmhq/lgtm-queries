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
 * @name Malformed id attribute
 * @description If the id of an HTML attribute is malformed, its
 *              interpretation may be browser-dependent.
 * @kind problem
 * @problem.severity warning
 * @id js/malformed-html-id
 * @tags maintainability
 *       correctness
 *       external/cwe/cwe-758
 * @precision very-high
 */

import javascript

from DOM::AttributeDefinition id, string reason
where DOM::isInvalidHtmlIdAttributeValue(id, reason) and
      // exclude attribute values that look like they might be templated
      not id.mayHaveTemplateValue()
select id, "The value of the id attribute " + reason + "."