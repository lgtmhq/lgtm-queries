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
 * @name Omitted array element
 * @description Omitted elements in array literals are easy to miss and should not be used.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       readability
 *       language-features
 * @precision very-high
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
  OmittedArrayElement() {
    hasOmittedElement()
  }

  /** Gets the index of the first omitted element in this array expression. */
  int getFirstOmittedElementIndex() {
    result = min(int i | elementIsOmitted(i))
  }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [LGTM locations](https://lgtm.com/docs/ql/locations).
   */
  predicate hasLocationInfo(string filepath, int startline, int startcolumn, int endline, int endcolumn) {
    exists (int i, Location pre, Location post |
      i = getFirstOmittedElementIndex() and
      pre = getTokenBeforeElement(i).getLocation() and
      post = getTokenAfterElement(i).getLocation() and
      filepath = pre.getFile().getAbsolutePath() and
      startline = pre.getStartLine() and
      startcolumn = pre.getStartColumn() and
      endline = post.getEndLine() and
      endcolumn = post.getEndColumn()
    )
  }

  /**
   * Gets the token after the `i`th element of this array expression.
   */
  Token getTokenAfterElement(int i) {
    i in [0..getSize()-1] and
    if exists(getElement(i)) then
      result = getElement(i).getLastToken().getNextToken()
    else if i = 0 then
      result = getFirstToken().getNextToken()
    else
      result = getTokenAfterElement(i-1).getNextToken()
  }

  /**
   * Gets the token before the `i`th element of this array expression.
   */
  Token getTokenBeforeElement(int i) {
    i in [0..getSize()-1] and
    if i = 0 then
      result = getFirstToken()
    else
      result = getTokenAfterElement(i-1)
  }
}

from OmittedArrayElement ae
select ae, "Avoid omitted array elements."