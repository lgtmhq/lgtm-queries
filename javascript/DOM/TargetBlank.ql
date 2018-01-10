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
 * @name Potentially unsafe external link
 * @description External links that open in a new tab or window but do not specify
 *              link type 'noopener' or 'noreferrer' are a potential security risk.
 * @kind problem
 * @problem.severity warning
 * @id js/unsafe-external-link
 * @tags maintainability
 *       security
 *       external/cwe/cwe-200
 * @precision very-high
 */

import javascript
import semmle.javascript.frameworks.Templating

/**
 * Holds if the attribute has a value that we can not determine statically.
 */
predicate hasDynamicHrefAttributeValue(DOM::ElementDefinition elem) {
  exists (DOM::AttributeDefinition attr |
    attr = elem.getAnAttribute() and
    attr.getName().matches("%href%") |
    not exists(attr.getStringValue()) or
    attr.getStringValue().regexpMatch(Templating::getDelimiterMatchingRegexp())
  )
}

from DOM::ElementDefinition e
where // `e` is a link that opens in a new browsing context (that is, it has `target="_blank"`)
      e.getName() = "a" and
      hasDynamicHrefAttributeValue(e) and
      e.getAttributeByName("target").getStringValue() = "_blank" and
      // there is no `rel` attribute specifying link type `noopener`/`noreferrer`;
      // `rel` attributes with non-constant value are handled conservatively
      forall (DOM::AttributeDefinition relAttr | relAttr = e.getAttributeByName("rel") |
        exists (string rel | rel = relAttr.getStringValue() |
          not exists (string linkType | linkType = rel.splitAt(" ") |
            linkType = "noopener" or
            linkType = "noreferrer"
          )
        )
      ) and
      // exclude elements with spread attributes or dynamically computed attribute names
      not exists (DOM::AttributeDefinition attr | attr = e.getAnAttribute() |
        not exists(attr.getName())
      )
select e, "External links without noopener/noreferrer are a potential security risk."
