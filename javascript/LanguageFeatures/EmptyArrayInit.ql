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
 * @name Omitted array element
 * @description Omitted elements in array literals are easy to miss and should not be used.
 * @kind problem
 * @problem.severity recommendation
 * @id js/omitted-array-element
 * @tags maintainability
 *       readability
 *       language-features
 * @precision high
 */

import javascript

/**
 * An initial omitted element in an array expression.
 *
 * This is represented by the corresponding array expression, with a special
 * `hasLocationInfo` implementation that assigns it a location covering the
 * first omitted array element.
 */
class OmittedArrayElement extends ArrayExpr {
  int idx;

  OmittedArrayElement() {
    idx = min(int i | elementIsOmitted(i))
  }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/help/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
    exists (Token pre, Location before, Location after |
      idx = 0 and pre = getFirstToken() or
      pre = getElement(idx-1).getLastToken().getNextToken() |
      before = pre.getLocation() and after = pre.getNextToken().getLocation() and
      before.hasLocationInfo(filepath, startline, startcolumn, _, _) and
      after.hasLocationInfo(_, _, _, endline, endcolumn)
    )
  }
}

from OmittedArrayElement ae
select ae, "Avoid omitted array elements."